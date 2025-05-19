
return_22: return_22.s
	gcc $< -o $@

return_22.i: return_22.c
	gcc -E -P return_22.c -o return_22.i

return_22.s: return_22.i
	gcc -S -O -fno-asynchronous-unwind-tables -fcf-protection=none return_22.i

return_2: return_2.s
	gcc $< -o $@

return_2.i: return_2.c
	gcc -E -P return_2.c -o return_2.i

return_2.s: return_2.i
	gcc -S -O -fno-asynchronous-unwind-tables -fcf-protection=none return_2.i

clean:
	rm -f return_2.i return_2.s return_2
	rm -f return_22.i return_22.s return_22
