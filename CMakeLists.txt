cmake_minimum_required(VERSION 3.15)
project(test_kyber C)

set(CMAKE_C_STANDARD 11)

include_directories(myref)


set(OPENSSL_ROOT_DIR /usr/local/opt/openssl@1.1/)
#set(OPENSSL_CRYPTO_LIBRARY /usr/local/opt/openssl/lib/)

find_package(OpenSSL REQUIRED)

if( OpenSSL_FOUND )
    include_directories(${OPENSSL_INCLUDE_DIR})
    link_directories(${OPENSSL_LIBRARIES})
    message(STATUS "Using OpenSSL ${OPENSSL_VERSION}")
endif()

add_compile_definitions(DKYBER_K=2)

add_executable(test_kyber
        myref/cbd.c
#        myref/cbd.h
        myref/fips202.c
#        myref/fips202.h
        myref/indcpa.c
#        myref/indcpa.h
#        myref/kem.c
        myref/ntt.c
#        myref/ntt.h
#        myref/params.h
        myref/poly.c
#        myref/poly.h
        myref/polyvec.c
#        myref/polyvec.h
        myref/randombytes.c
#        myref/randombytes.h
        myref/reduce.c
#        myref/reduce.h
#        myref/rng.c
        myref/rng.h
#        myref/sha2.h
        myref/sha256.c
        myref/sha512.c
        myref/symmetric-shake.c
#        myref/symmetric.h
        myref/test_kyber.c
#        myref/verify.c
#        myref/verify.h
        )
