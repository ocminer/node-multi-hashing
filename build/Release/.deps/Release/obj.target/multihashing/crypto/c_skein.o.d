cmd_Release/obj.target/multihashing/crypto/c_skein.o := cc '-D_LARGEFILE_SOURCE' '-D_FILE_OFFSET_BITS=64' '-DBUILDING_NODE_EXTENSION' -I/home/marcel/.node-gyp/0.10.35/src -I/home/marcel/.node-gyp/0.10.35/deps/uv/include -I/home/marcel/.node-gyp/0.10.35/deps/v8/include -I../crypto  -fPIC -Wall -Wextra -Wno-unused-parameter -pthread -m64 -O2 -fno-strict-aliasing -fno-tree-vrp -fno-omit-frame-pointer  -MMD -MF ./Release/.deps/Release/obj.target/multihashing/crypto/c_skein.o.d.raw  -c -o Release/obj.target/multihashing/crypto/c_skein.o ../crypto/c_skein.c
Release/obj.target/multihashing/crypto/c_skein.o: ../crypto/c_skein.c \
 ../crypto/c_skein.h ../crypto/skein_port.h ../crypto/int-util.h \
 ../crypto/hash.h ../crypto/hash-ops.h
../crypto/c_skein.c:
../crypto/c_skein.h:
../crypto/skein_port.h:
../crypto/int-util.h:
../crypto/hash.h:
../crypto/hash-ops.h:
