
# Build commands for bitcode

.SUFFIXES: .c .bc

artifacts/linked.bc : artifacts/gf.bc artifacts/root.bc artifacts/util.bc artifacts/synd.bc artifacts/transpose.bc artifacts/bm.bc artifacts/encrypt.bc artifacts/controlbits.bc artifacts/pk_gen.bc
	llvm-link artifacts/gf.bc artifacts/root.bc artifacts/util.bc artifacts/synd.bc artifacts/transpose.bc artifacts/bm.bc artifacts/encrypt.bc artifacts/controlbits.bc artifacts/pk_gen.bc -o artifacts/linked.bc

artifacts/synd.bc : imp-custom/synd.c
	clang -g -O0 -c -emit-llvm $< -o $@ -march=native -mtune=native -Wall -I. -Isubroutines -DKAT -DKATNUM=`cat imp/KATNUM` "-DCRYPTO_NAMESPACE(x)=x" "-D_CRYPTO_NAMESPACE(x)=_##x"

artifacts/bm.bc : imp-custom/bm.c
	clang -g -O0 -c -emit-llvm $< -o $@ -march=native -mtune=native -Wall -I. -Isubroutines -DKAT -DKATNUM=`cat imp/KATNUM` "-DCRYPTO_NAMESPACE(x)=x" "-D_CRYPTO_NAMESPACE(x)=_##x"

artifacts/encrypt.bc : imp-custom/encrypt.c
	clang -g -O0 -c -emit-llvm $< -o $@ -march=native -mtune=native -Wall -I. -Isubroutines -DKAT -DKATNUM=`cat imp/KATNUM` "-DCRYPTO_NAMESPACE(x)=x" "-D_CRYPTO_NAMESPACE(x)=_##x"

artifacts/pk_gen.bc : imp-custom/pk_gen.c
	clang -g -O0 -c -emit-llvm $< -o $@ -march=native -mtune=native -Wall -I. -Isubroutines -DKAT -DKATNUM=`cat imp/KATNUM` "-DCRYPTO_NAMESPACE(x)=x" "-D_CRYPTO_NAMESPACE(x)=_##x"

artifacts/%.bc : imp/%.c
	clang -g -O0 -c -emit-llvm $< -o $@ -march=native -mtune=native -Wall -I. -Isubroutines -DKAT -DKATNUM=`cat imp/KATNUM` "-DCRYPTO_NAMESPACE(x)=x" "-D_CRYPTO_NAMESPACE(x)=_##x"

graph : graphs/graph.dot
	dot -Tpng $< > artifacts/graph.png

test-log: artifacts/linked.bc
	saw -s artifacts/proof_output --summary-format=pretty proofs/linked.saw 

test: clean artifacts/linked.bc
	saw proofs/linked.saw 

clean:
	rm -f artifacts/*

