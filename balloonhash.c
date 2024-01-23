/*
    Balloon Hashing. A memory-hard password hashing algorithm.

    Original algorithm by Dan Boneh, Henry Corrigan-Gibbs, and Stuart Schechter.
    Implementation by Jeremy Ong.

    A parallelized implementation of balloon hashing, a tunable, memory-hard
    hash algorithm. This implementation uses SHA256 as a subroutine. Other
    subroutine hash algorithms can be substituted with minor adjustments.
    Fixed-width integers are used for compatibility across architectures.
    However, systems using char types greater than 8 bits or byte sizes other
    than 8 bits may not work correctly.


    Adjustable parameters:
     - HASH_SIZE: The size in bytes of the hash output of the subroutine hash
         algorithm. Balloon hashing's final output will inherit this size. Must
         be at least 4 bytes.
     - S_COST: Space cost factor. Algorithm will require S_COST * HASH_SIZE
         total bytes to be kept in memory for the duration of execution.
         Execution time is also increased by a factor of S_COST.
     - T_COST: Time cost factor. Number of rounds of hashing to be performed.
     - DELTA: Block dependency factor. Should be >= 2 to avoid potential attack
         on memory access pattern, which may reduce memory needed for execution.
         Execution time is also increased by a factor of DELTA.
     - P: Parallelization factor. Number of parallel hash threads to use.
         Total work (but not necessarily execution time) is increased by a
         factor of P. Must be least 1.
     - SALT: Salt to apply to hash. Must be of at least HASH_SIZE. Any excess
         beyond HASH_SIZE will be ignored. Will not be used if custom_salt is
         specified in call to balloonhash_p.

    For best resistance to attack, parameters should be tuned. S_COST should be
    set so as to use the maximum tolerable memory on the target system. T_COST
    should be set so as to use the maximum tolerable time. A value of 3 for
    DELTA is likely sufficient. If there is concern about a vulnerability in
    the memory access pattern, DELTA can be increased (with a proportional
    increase in execution time). P can be set to take advantage of additional
    processors on target system.
*/

#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <openssl/sha.h>

#define HASH_SIZE 32

const long int S_COST = 10000;
const int T_COST = 10;
const int DELTA = 3;
const int P = 4;
const uint8_t SALT[HASH_SIZE] = {0x94, 0x3f, 0x67, 0xf4, 0x94, 0x63, 0xe0, 0x00,
                                 0x42, 0x87, 0x16, 0x83, 0x6f, 0xfe, 0x31, 0x77,
                                 0xc2, 0x32, 0xa5, 0x8c, 0xd4, 0x54, 0x9f, 0x7a,
                                 0xe9, 0x51, 0x6d, 0x6d, 0x78, 0x61, 0x3c, 0xb8};

struct block_t
{
    uint8_t data[HASH_SIZE];
};

struct args_t
{
    void *message;
    size_t message_len;
    struct block_t *digest;
    const void *custom_salt;
};

/*
    Wrapper for subroutine hash function (currently SHA256). Concatenates up to
    three inputs and passes the value to the specified hash algorithm.

     - input1, input2, input3: Inputs into the hash function.
         NULL values will result in undefined behavior, even with length of 0.
     - input1_len, input2_len, input3_len: Lengths of respective input messages.
     - digest: Pointer to hash output.
         Must have at least HASH_SIZE bytes allocated.
*/
void hash_subroutine(const void *input1, size_t input1_len,
                     const void *input2, size_t input2_len,
                     const void *input3, size_t input3_len,
                     void *digest)
{
    char *message = malloc(input1_len + input2_len + input3_len);
    memcpy(message, input1, input1_len);
    memcpy(message + input1_len, input2, input2_len);
    memcpy(message + input1_len + input2_len, input3, input3_len);

    SHA256(message, input1_len + input2_len + input3_len, digest);
    free(message);
}

/*
    Print block and message string for debugging purposes.

     - block: Pointer to any data of size HASH_SIZE to be printed.
     - message: String to be printed.
*/
void pb(void *block, char *message)
{
    unsigned char *temp = (unsigned char*)block;

    for (int i = 0; i < HASH_SIZE; i++)
    {
        printf("%02x", temp[i]);
    }
    printf(" %s\n", message);
}

/*
    Serial ballon hash algorithm for passing to pthread_create.

     - args_pointer.message: Input to be hashed.
     - args_pointer.message_len: Length in bytes of message.
     - args_pointer.digest: Pointer to hash output.
         Must have at least HASH_SIZE bytes allocated.
     - args_pointer.custom_salt: Salt to use in hash function.
         If custom_salt is NULL, use hard-coded SALT constant instead.
         Must have at least HASH_SIZE bytes allocated.
*/
void *balloonhash_thread(void *args_pointer)
{
    struct args_t *args = (struct args_t*)args_pointer;
    // Hash counter to ensure every hash input is unique (for provability).
    uint64_t cnt = 0;
    struct block_t *buf = malloc(HASH_SIZE * S_COST);
    if (args->custom_salt == NULL)
    {
        args->custom_salt = SALT;
    }

    hash_subroutine(&cnt, sizeof(cnt),
                    args->message, args->message_len,
                    args->custom_salt, HASH_SIZE, buf);
    cnt++;
    for (int m = 1; m < S_COST; m++)
    {
        hash_subroutine(&cnt, sizeof(cnt),
                        buf + m - 1, HASH_SIZE,
                        "", 0, buf + m);
        cnt++;
    }

    for (uint32_t t = 0; t < T_COST; t++)
    {
        for (uint32_t m = 0; m < S_COST; m++)
        {
            if (m == 0)
            {
                hash_subroutine(&cnt, sizeof(cnt),
                                buf + S_COST - 1, HASH_SIZE,
                                buf, HASH_SIZE, buf);
            }
            else
            {
                hash_subroutine(&cnt, sizeof(cnt),
                                buf + m - 1, HASH_SIZE,
                                buf + m, HASH_SIZE, buf + m);
            }
            cnt++;

            for (uint32_t i = 0; i < DELTA; i++)
            {
                struct block_t idx_block;
                struct block_t other_block;
                hash_subroutine(&t, sizeof(t),
                                &m, sizeof(m),
                                &i, sizeof(i), &idx_block);
                hash_subroutine(&cnt, sizeof(cnt),
                                args->custom_salt, HASH_SIZE,
                                &idx_block, HASH_SIZE, &other_block);
                cnt++;
                // Select block pseudorandomly.
                uint32_t index;
                memcpy(&index, other_block.data, sizeof(index));
                hash_subroutine(&cnt, sizeof(cnt),
                                buf + m, HASH_SIZE,
                                buf + (index % S_COST), HASH_SIZE, buf + m);
                cnt++;
            }
        }
    }

    hash_subroutine(args->message, args->message_len,
                    args->custom_salt, HASH_SIZE,
                    buf + S_COST - 1, HASH_SIZE, args->digest);
    free(buf);
}

/*
    Parallelized balloon hash algorithm.

     - message: Input to be hashed.
     - message_len: Length in bytes of message.
     - digestptr: Pointer to hash output.
         Must have at least HASH_SIZE bytes allocated.
     - custom_salt: Salt to use in hash function.
         If custom_salt is NULL, use hard-coded SALT constant instead.
         Must have at least HASH_SIZE bytes allocated.
*/
void balloonhash_p(const void *message, size_t message_len, void *digestptr,
                   const void *custom_salt)
{
    struct block_t *digest = (struct block_t*) digestptr;
    pthread_t ids[P];
    struct args_t args[P];
    unsigned char *thread_messages[P];
    struct block_t thread_digests[P];
    memset(digest, 0, HASH_SIZE);

    for (uint32_t i = 0; i < P; i++)
    {
        thread_messages[i] = malloc(message_len + sizeof(i));
        memcpy(thread_messages[i], message, message_len);
        memcpy(thread_messages[i] + message_len, &i, sizeof(i));
        args[i].message = thread_messages[i];
        args[i].message_len = message_len + sizeof(i);
        args[i].digest = thread_digests + i;
        args[i].custom_salt = custom_salt;
        if (pthread_create(ids + i, NULL, balloonhash_thread, args + i) != 0)
        {
            perror("Error creating thread in function balloonhash_p.");
            exit(1);
        }
    }

    for (int i = 0; i < P; i++)
    {
        if (pthread_join(ids[i], NULL) != 0)
        {
            perror("Error exiting thread in function balloonhash_p.");
            exit(1);
        }
        free(thread_messages[i]);

        for (int j = 0; j < HASH_SIZE; j++)
        {
            digest->data[j] ^= thread_digests[i].data[j];
        }
    }
}

