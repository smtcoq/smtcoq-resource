ZCHAFFSRC=$(wildcard sat*.cnf) hole4.cnf cmu-bmc-barrel6.cnf velev-sss-1.0-05.cnf
VERITSRC=$(wildcard sat*.smt2) hole4.smt2 $(wildcard uf*.smt2) $(wildcard lia*.smt2) $(wildcard let*.smt2)
ZCHAFFLOG=$(ZCHAFFSRC:.cnf=.zlog)
VERITLOG=$(VERITSRC:.smt2=.vtlog)
#OBJ=$(ZCHAFFLOG) $(VERITLOG)
OBJ=$(ZCHAFFLOG) 


all: $(OBJ)


%.zlog: %.cnf
	./runzchaff.sh $<


%.vtlog: %.smt2
	./runverit.sh $<


clean:
	rm -rf *~ *.zlog *.vtlog
