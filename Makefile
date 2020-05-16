all : util.vo strt.vo strt.html strt2.vo strt2.html atan2.vo atan2.html ttyp.vo ttyp.html tdyn.vo tdyn.html ttim.vo tlens.vo tlens.html incr_function_le_ep.vo dtlen.vo dtlen.html

util.vo: util.v
	coqc util.v

atan2.vo : atan2.v util.vo
	coqc atan2.v

ttyp.vo : ttyp.v util.vo atan2.vo
	coqc ttyp.v

strt.vo : strt.v ttyp.vo util.vo atan2.vo
	coqc strt.v

strt2.vo : strt2.v strt.vo ttyp.vo util.vo atan2.vo
	coqc strt2.v

tdyn.vo : tdyn.v ttyp.vo util.vo atan2.vo
	coqc tdyn.v

ttim.vo : ttim.v ttyp.vo
	coqc ttim.v

tlens.vo : tlens.v util.vo atan2.vo incr_function_le_ep.vo
	coqc tlens.v

dtlen.vo : dtlen.v tlens.vo util.vo atan2.vo incr_function_le_ep.vo
	coqc dtlen.v

incr_function_le_ep.vo : incr_function_le_ep.v util.vo
	coqc incr_function_le_ep.v

atan2.html : atan2.vo atan2.v
	coqdoc -g -utf8 atan2.v


tdyn.html : tdyn.vo tdyn.v
	coqdoc -g -utf8 tdyn.v

ttyp.html : ttyp.vo ttyp.v
	coqdoc -g -utf8 ttyp.v

strt.html : strt.vo strt.v
	coqdoc -g -utf8 strt.v

strt2.html : strt2.vo strt2.v
	coqdoc -g -utf8 strt2.v

tlens.html : tlens.vo tlens.v
	coqdoc -g -utf8 tlens.v

dtlen.html : dtlen.vo dtlen.v
	coqdoc -g -utf8 dtlen.v

clean :
	rm *.vo *.glob
