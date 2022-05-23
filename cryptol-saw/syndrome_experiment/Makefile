
%.out : %.c
	clang -O3 $< -o $@

test: syndrome.out my_syndrome.out
	echo "syndrome:"
	time -p ./syndrome.out 69
	echo "my_syndrome:"
	time -p ./my_syndrome.out 69

clean:
	rm *.out