.text
.globl other_print_hello_0
other_print_hello_0:
	pushq %rbp
	movq %rsp, %rbp
	leaq dsval_0(%rip), %rsi
	leaq fmt_str(%rip), %rdi
	callq printf
	leave
	ret
.type other_print_hello_0, @function
.size other_print_hello_0, .-other_print_hello_0
/* end function other_print_hello_0 */

.text
.globl other_submod_print_bye_0
other_submod_print_bye_0:
	pushq %rbp
	movq %rsp, %rbp
	leaq dsval_1(%rip), %rsi
	leaq fmt_str(%rip), %rdi
	callq printf
	leave
	ret
.type other_submod_print_bye_0, @function
.size other_submod_print_bye_0, .-other_submod_print_bye_0
/* end function other_submod_print_bye_0 */

.data
.balign 8
fmt_uint:
	.ascii "%lu\n"
/* end data */

.data
.balign 8
fmt_int:
	.ascii "%ld\n"
/* end data */

.data
.balign 8
fmt_float:
	.ascii "%f\n"
/* end data */

.data
.balign 8
fmt_str:
	.ascii "%s\n"
/* end data */

.data
.balign 8
dsval_0:
	.ascii "Hello, modules!"
	.byte 0
/* end data */

.data
.balign 8
dsval_1:
	.ascii "Goodbye!"
	.byte 0
/* end data */

.section .note.GNU-stack,"",@progbits
