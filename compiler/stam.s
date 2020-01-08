"mov rbx, [rbp + 8*2] ;;rbx = address of env
mov rcx, 0 ;;counter for size of env
count_env_length: ;;add index!!!!!!!!
    cmp [rbx], SOB_NIL_ADDRESS
    je end_count_env_length 
    add rbx, 8
    add rcx, 1 
    jmp count_env_length
end_count_length: ;;add index!!!!!!
    push rcx
    add rcx,1 ;;size of extent env 
    mul rcx, 8
    MALLOC rax, rcx 
    pop rcx ;;env size 
    mov rbx, [rbp + 8*2] 
;;rbx is oldenv adrees and rax is extenvadrees
    mov rsi 0 ;;i
    mov rdi 1 ;;j
copy_old_env: ;;add indx!!!!
    cmp rsi, rcx
    je end_copy_old_env 
    mov rdx, [rbx + 8*rsi] ;;Env[i]
    mov [rax + 8*rdi], rdx ;;ExtEnv[j] = Env[i]
    inc rsi
    inc rdi 
    jmp copy_old_env

end_copy_old_env: ;;add index!!!!!!!!
    mov rdx, [rbp + 8*3]
    push rax
    push rdx 
    mul rdx, 8
    MALLOC rbx, rdx ;;rbx is address of ExtEnv[0]
    pop rax ;;address of ExtEnv
    pop rdx ;;number of params 
    mov [rax], rbx  ;;put ExtEnv[0] address in ExtEnv Vector 
;;rbx is the pointer to the extenv[0] and rdx number of params 
    mov rcx,0
compy_params:
    cmp rcx, rdx 
    je end_copy_params 
    mov rsi, rcx 
    mul rsi, 8 ;;for param number rcx 
    add rsi, 4*8 ;;for the zeroth param
    add rsi, rbp 
    ;;[rbp + 4*8 + rcx*8]
    mov rsi, [rsi]
    mov [rbx+rcx*8], rsi 
    inc rcx 
    jmp compy_params
end_copy_params:
    mov rbx, rax 
    MAKE_CLOSURE(rax, rbx ,Lcode) ;;add index!!!!!!!!!!!!!!!!
    jmp Lcont ;;add index!!!!!!!!!!!!!!!!
Lcode:;;add index!!!!!!!!!!!!!!!!
    push rbp
    mov rbp, rsp "






 "   leave
    ret 
Lcont:;;add index!!!!!!!!!!!!!!!!"



