all: RiseDecoupled.vo FallDecoupled.vo

Monad.vo: Monad.v
	coqc Monad.v

Base.vo: Base.v Monad.vo
	coqc Base.v

FlowEquivalence.vo: FlowEquivalence.v Monad.vo Base.vo
	coqc FlowEquivalence.v

RiseDecoupled.vo: RiseDecoupled.v FlowEquivalence.vo Monad.vo Base.vo
	coqc RiseDecoupled.v

FallDecoupled.vo: FallDecoupled.v FlowEquivalence.vo Monad.vo Base.vo
	coqc FallDecoupled.v
