MACHINE
    EstoqueMedicamento

SETS 
    NOME
     
VARIABLES
    estoque, dia, medicamento, vencidos
    
INVARIANT
    medicamento : NAT +-> NOME * NAT1 * NAT1 &
    estoque : NAT +-> NAT &
    dom(estoque) = dom(medicamento) &
    dia : NAT & // com a nova modelagem, dia ainda eh necessario?
    vencidos : NAT >-> dom(medicamento)
    
INITIALISATION
    medicamento := {} 
    || estoque := {} 
    || dia := 1 
    || vencidos := (0..card(medicamento))*{0}
    
OPERATIONS

    adicionar_medicamento(ID , nome, lote, validade) =
        PRE nome: NOME & lote: NAT1 & validade: NAT1 & ID : NAT & ID /: dom(medicamento)
        THEN medicamento := medicamento \/ {ID |-> (nome |-> lote |-> validade)} 
                || estoque := estoque \/ {ID |-> 0}
        END;

    remover_medicamento(ID) = 
        PRE ID : NAT & ID : dom(medicamento)
        THEN medicamento := medicamento - ({ID} <| medicamento) 
            || estoque := estoque -  ({ID} <| estoque)
        END;

    adicionar_estoque(ID, qtd) = 
        PRE ID: NAT & ID : dom(medicamento) & qtd : NAT1 & estoque(ID) + qtd : NAT
        THEN estoque(ID) := estoque(ID) + qtd
        END;

    remover_estoque(ID, qtd) = 
        PRE ID: NAT & ID : dom(medicamento) & qtd : NAT1 & (estoque(ID) - qtd) >= 0 
        THEN estoque(ID) := estoque(ID) - qtd
        END;

    qtd <-- qtd_medicamento(ID) = 
        PRE ID : dom(medicamento)
        THEN qtd := estoque(ID)
        END;

    incrementar_dia = 
        BEGIN 
            dia := dia + 1 
        END;

    hoje <-- consultar_dia = 
        BEGIN
            hoje := dia
        END;
        
    vv <-- verificar_vencidos = 
        BEGIN
            // vencidos(vv) eh a qtd de dias desde 1/1/1xxx (dia 0);
            // isso indica qntd dias dps do dia 1/1/1xxx o medicamento vence.
            // se a data eh contabilizada assim, 
            // entao estar vencido = vencidos(vv) < a qtd de dias desde 1/1/1xxx ate hj.
            // esse "0" eh onde vai vir "a qtd de dias desde 1/1/1xxx ate hj".
            // como fazer isso?
            vv := {xx | xx : dom(medicamento) & vencidos(vv) < 0}
        END
END