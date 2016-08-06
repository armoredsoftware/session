all:
	coqc CpdtTactics.v
	coqc Crypto.v
	coqc ProtoRep.v
	coqc SfLib.v
	coqc ProtoStateSemantics.v

clean:
	$(RM) *.vo
	$(RM) *.glob
	$(RM) *.aux
