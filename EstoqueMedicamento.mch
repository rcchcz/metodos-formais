MACHINE
    EstoqueMedicamento

SETS 
    NOME
    
CONSTANTS
    limit, empty
    
PROPERTIES
    limit : NAT & empty : NOME
     
VARIABLES
    estoque, dia, medicamento
    
INVARIANT
    medicamento : NAT +-> NOME * NAT * NAT &
    estoque : NAT +-> NAT &
    dom(estoque) = dom(medicamento) &
    dia : NAT &
    dom(medicamento) : FIN(NAT)
    
INITIALISATION
    medicamento := {} 
    || estoque := {} 
    || dia := 0
    
OPERATIONS
    adicionar_medicamento(ID , nome, lote, validade) =
        PRE nome: NOME & lote: NAT & validade: NAT & ID : NAT & ID /: dom(medicamento)
        THEN medicamento := medicamento \/ {ID |-> (nome |-> lote |-> validade)} 
                || estoque := estoque \/ {ID |-> 0}
        END;

    remover_medicamento(ID) = 
        PRE ID : NAT & ID : dom(medicamento)
        THEN medicamento := medicamento - ({ID} <| medicamento) 
            || estoque := estoque -  ({ID} <| estoque)
        END;

    adicionar_estoque(ID, qtd) = 
        PRE ID: NAT & ID : dom(medicamento) & qtd : NAT & estoque(ID) + qtd : NAT
        THEN estoque(ID) := estoque(ID) + qtd
        END;

    remover_estoque(ID, qtd) = 
        PRE ID: NAT & ID : dom(medicamento) & qtd : NAT & (estoque(ID) - qtd) >= 0 
        THEN estoque(ID) := estoque(ID) - qtd
        END;
    /*
    qtd <-- qtd_medicamento(ID) = 
        PRE ID : dom(medicamento)
        THEN qtd := estoque(ID)
        END;
    */
    incrementar_dia = 
        PRE dia + 1 : NAT
        THEN dia := dia + 1 
        END;

    hoje <-- consultar_dia = 
        BEGIN
            hoje := dia
        END
    /*    
    oo <-- verificar_validade(xx) = 
        PRE xx : dom(medicamento)
        THEN
            oo := max({0, min(ran(medicamento[{xx}])) - dia}) 
        END
    */
END
