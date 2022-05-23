
%.out : %.c
	clang -O3 $< -o $@

test: synd.out my_synd.out
	echo "synd:"
	time -p ./synd.out 69
	echo "my_synd:"
	time -p ./my_synd.out 69

clean:
	rm *.out