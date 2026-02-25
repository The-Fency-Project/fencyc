.text
.globl main
main:
	pushq %rbp
	movq %rsp, %rbp
	callq main_main_0
	movl $0, %eax
	leave
	ret
.type main, @function
.size main, .-main
/* end function main */

.text
main_main_0:
	pushq %rbp
	movq %rsp, %rbp
	callq other_print_hello_0
	callq other_submod_print_bye_0
	leave
	ret
.type main_main_0, @function
.size main_main_0, .-main_main_0
/* end function main_main_0 */

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

.section .note.GNU-stack,"",@progbits
