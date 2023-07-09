MACHINE
    EstoqueMedicamento

SETS 
    NOME
     
VARIABLES
    estoque, dia, medicamento
    
INVARIANT
    medicamento : NAT +-> NOME * NAT1 * NAT1 &
    estoque : NAT +-> NAT &
    dom(estoque) = dom(medicamento) &
    dia : NAT
    
INITIALISATION
    medicamento := {} 
    || estoque := {} 
    || dia := 0
    
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
            vv := {xx | xx : dom(medicamento) & #(yy) . (yy:ran(medicamento[{xx}]) & yy < dia)}
        END
END