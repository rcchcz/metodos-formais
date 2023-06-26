MACHINE
    EstoqueMedicamento

SETS 
    NOME
     
VARIABLES
    estoque, dia, medicamento
    
INVARIANT
    medicamento : NATURAL +-> NOME * NATURAL1 * NATURAL1 &
    estoque : dom(medicamento) +-> NATURAL &
    dia : NATURAL1
    
INITIALISATION
 medicamento := {} || estoque := {} || dia := 1
    
OPERATIONS

    adicionar_medicamento(ID , nome, lote, validade) =
    PRE nome: NOME & lote: NATURAL1 & validade: NATURAL1 & ID : NATURAL & ID /: dom(medicamento)
    THEN medicamento := medicamento \/ {ID |-> (nome |-> lote |-> validade)} || estoque := estoque \/ {ID |-> 0}
    END;

    remover_medicamento(ID) = 
    PRE ID : NATURAL & ID : dom(medicamento)
    THEN medicamento := medicamento - ({ID} <| medicamento) || estoque := estoque -  ({ID} <| estoque)
    END;

    adicionar_estoque(ID, qtd) = 
    PRE ID: NATURAL & ID : dom(medicamento) & qtd : NATURAL1 & estoque(ID) + qtd : NATURAL
    THEN estoque(ID) := estoque(ID) + qtd
    END;

    remover_estoque(ID, qtd) = 
    PRE ID: NATURAL & ID : dom(medicamento) & qtd : NATURAL1 & estoque(ID) > 0
    THEN estoque(ID) := max({estoque(ID) - qtd,  0})
    END;

    qtd <-- qtd_medicamento(ID) = 
    PRE ID : dom(medicamento)
    THEN qtd := estoque(ID)
    END;

    incrementar_dia = 
    PRE dia < 30
    THEN dia := dia + 1
    END;

    hoje <-- consultar_dia = 
    PRE 1=1
    THEN hoje := dia
    END;
    
    vencidos <-- verificar_vencidos(xx) = 
    PRE xx:medicamento
    THEN 
	ANY aa,vv WHERE aa : dom({xx}) & vv : ran(ran({xx}))
		THEN 
			vencidos := {xx | xx : dom(medicamento) & (estoque(aa) > 0) & vv < dia}
	END
    END
END