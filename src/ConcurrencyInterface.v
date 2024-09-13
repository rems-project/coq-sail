
Require Import Strings.String.
Require Import stdpp.bitvector.definitions.
Require Import stdpp.countable.

(* For choice outcomes *)
Require Import Sail.Values.
(* This is needed because sail cannot export into multiple Coq files *)
Require Import Sail.ConcurrencyInterfaceTypes.

Local Open Scope stdpp_scope.
Local Open Scope Z_scope.

Inductive empOutcome (R : Type) :=.

(** The architecture parameters that must be provided to the interface *)
Module Type Arch.

  (** The type of registers, parametrised by the type of values for that register *)
  Parameter reg : Type -> Type.

  (** We need to implement a gmap indexed by registers *)
  Parameter reg_eq : ∀ A, EqDecision (reg A).
  #[export] Existing Instance reg_eq.
  (* This would be nice, but it essentially involves inverting reg A, which doesn't seem to be
     possible in a useful way.
  Parameter reg_countable : ∀ A, Countable (reg A).
  #[export] Existing Instance reg_countable.
  *)

  Inductive greg := GReg (A : Type) (r : reg A).
  #[global] Arguments GReg [_] _.
  #[global] Coercion GReg : reg >-> greg.

  Parameter greg_eq : EqDecision greg.
  #[export] Existing Instance greg_eq.

  Parameter greg_cnt : Countable greg.
  #[export] Existing Instance greg_cnt.

  #[export] Hint Extern 1 (reg _) => assumption : typeclass_instances.
  Parameter regval_inhabited : ∀ A, reg A → Inhabited A.
  #[export] Existing Instance regval_inhabited.
  Parameter regval_eq : ∀ A, reg A → EqDecision A.
  #[export] Existing Instance regval_eq.
  Parameter regval_cnt : ∀ A (r : reg A), Countable A.
  #[export] Existing Instance regval_cnt.

  (** From a register equality proof, we need to transport a register value.
      This must compute (with vm_compute) even if the proof is opaque, For Ocaml
      extraction, this should be extracted to Obj.magic *)
  Parameter regval_transport:
    ∀ {A B} {rA : reg A} {rB : reg B}, rA =@{greg} rB → A → B.

  (** Soundness proof for [regval_extract] *)
  Parameter regval_transport_sound:
    ∀ A (r r' : reg A) (e : r =@{greg} r') a,
    regval_transport e a = a.

  (** Virtual address size *)
  Parameter va_size : N.

  (** Physical addresses type. Since models are expected to be architecture
      specific in this, there is no need for a generic way to extract a
      bitvector from it*)
  Parameter pa : Type.

  (** We need to implement a gmap indexed by pa *)
  Parameter pa_eq : EqDecision pa.
  #[export] Existing Instance pa_eq.
  Parameter pa_countable : @Countable pa pa_eq.
  #[export] Existing Instance pa_countable.

  (** Parameter for extra architecture specific access types. Can be an empty
      type if not used *)
  Parameter arch_ak : Type.
  Parameter arch_ak_eq : EqDecision arch_ak.
  #[export] Existing Instance arch_ak_eq.

  (** Translation summary *)
  Parameter translation : Type.
  Parameter translation_eq : EqDecision translation.
  #[export] Existing Instance translation_eq.

  (** Abort description. This represent physical memory aborts on memory
      accesses, for example when trying to access outside of physical memory
      range. Those aborts are generated by the model*)
  Parameter abort : Type.
  Parameter abort_eq : EqDecision abort.
  #[export] Existing Instance abort_eq.

  (** Barrier types *)
  Parameter barrier : Type.
  Parameter barrier_eq : EqDecision barrier.
  #[export] Existing Instance barrier_eq.

  (** Cache operations (data and instruction caches) *)
  Parameter cache_op : Type.
  Parameter cache_op_eq : EqDecision cache_op.
  #[export] Existing Instance cache_op_eq.

  (** TLB operations *)
  Parameter tlb_op : Type.
  Parameter tlb_op_eq : EqDecision tlb_op.
  #[export] Existing Instance tlb_op_eq.

  (** Fault type for a fault raised by the instruction (not by the concurrency model)
      In Arm terms, this means any synchronous exception decided by the ISA model *)
  Parameter fault : Type.
  Parameter fault_eq : EqDecision fault.
  #[export] Existing Instance fault_eq.
End Arch.

Module Interface (A : Arch).
  Import A.

  Definition va := bv va_size.
  Definition accessKind := Access_kind arch_ak.

  Module ReadReq.
    Record t {deps : Type} {n : N} :=
      make
        { pa : pa;
          access_kind : accessKind;
          va : option va;
          translation : translation;
          tag : bool;
          addr_deps : deps;
        }.
    Arguments t : clear implicits.

    Definition set_deps {d1 d2 : Type} {n : N} (f : d1 -> d2) (rr : t d1 n)
      : t d2 n :=
      {|
        pa := rr.(pa);
        access_kind := rr.(access_kind);
        va := rr.(va);
        translation := rr.(translation);
        tag := rr.(tag);
        addr_deps := f rr.(addr_deps);
        |}.

    Definition setv_deps {d1 d2 : Type} {n : N} (adeps : d2) (rr : t d1 n) :=
      set_deps (fun _ => adeps) rr.

  End ReadReq.

  Module WriteReq.
    Record t {deps : Type} {n : N} :=
      make
        { pa : pa;
          access_kind : accessKind;
          value : bv (8 * n);
          va : option va;
          translation : A.translation;
          tag : option bool;
          addr_deps : deps;
          data_deps : deps;
        }.
    Arguments t : clear implicits.

    Definition set_deps {d1 d2 : Type} {n : N} (f : d1 -> d2) (wr : t d1 n)
      : t d2 n :=
      {|
        pa := wr.(pa);
        access_kind := wr.(access_kind);
        value := wr.(value);
        va := wr.(va);
        translation := wr.(translation);
        tag := wr.(tag);
        addr_deps := f wr.(addr_deps);
        data_deps := f wr.(data_deps);
        |}.

    Definition setv_deps {d1 d2 : Type} {n : N} (adeps ddeps : d2)
      (wr : t d1 n) : t d2 n:=
      {|
        pa := wr.(pa);
        access_kind := wr.(access_kind);
        value := wr.(value);
        va := wr.(va);
        translation := wr.(translation);
        tag := wr.(tag);
        addr_deps := adeps;
        data_deps := ddeps;
        |}.

  End WriteReq.

  Section T.
    Context {deps : Type}.
    Context {eOutcome : Type -> Type}.

  Inductive outcome : Type -> Type :=
    (** The direct or indirect flag is to specify how much coherence is required
        for relaxed registers *)
  | RegRead {T : Type} (reg : reg T) (direct : bool) : outcome T

    (** The direct or indirect flag is to specify how much coherence is required
        for relaxed registers.

        The dep_on would be the dependency of the register write.

        Generally, writing the PC introduces no dependency because control
        dependencies are specified by the branch announce *)
  | RegWrite {T : Type} (reg : reg T) (direct : bool) (deps : deps)
             (regval: T) : outcome unit
  | MemRead (n : N) : ReadReq.t deps n ->
                      outcome (bv (8 * n) * option bool + abort)
  | MemWrite (n : N) : WriteReq.t deps n -> outcome (option bool + abort)
    (** Declare the opcode of the current instruction when known. Used for
        dependency computation *)
  | InstrAnnounce (opcode : bvn) : outcome unit
    (** The deps here specify the control dependency *)
  (* TODO: resolve this: The SSC definition is
  | BranchAnnounce (pa : pa) (deps : deps) : outcome unit
     but the Sail library is *)
  | BranchAnnounce sz (pa : mword sz) (deps : deps) : outcome unit
  | Barrier : barrier -> outcome unit
  | CacheOp (deps : deps) : cache_op -> outcome unit
  | TlbOp (deps : deps) : tlb_op -> outcome unit
  | TakeException : fault -> outcome unit
  | ReturnException (pa : pa) : outcome unit

  (** Custom outcome to support simplified models on either side that want
      symbolic outcomes. This can be use to represent abstracted sail function
      for example the Arm translation function *)
  | ExtraOutcome {A} : eOutcome A -> outcome A

  (** Bail out when something went wrong; this may be refined in the future.
      This is an ISA model triggered failure *)
  | GenericFail (msg : string) : outcome False

  | CycleCount : outcome unit
  | GetCycleCount : outcome Z

  (** The next two outcomes are for handling non-determinism. Choose will branch
      the possible executions non-deterministically for every value of the
      type given by the code *)
  | Choose ty : outcome (choose_type ty)
  (** Discard means that the instruction could never have made the previous
      non-deterministic choices and the current execution can be silently
      discarded. *)
  | Discard : outcome False.


  (********** Monad instance **********)

  (** This is a naive but inefficient implementation of the instruction monad.
      It might be replaced by an more efficient version later. *)
  (* TODO: Do something like itrees to take the full outcome type as a
     parameter *)
  Inductive iMon {A : Type} :=
  | Ret : A -> iMon
  | Next {T : Type} : outcome T -> (T -> iMon) -> iMon.
  Arguments iMon : clear implicits.

  Global Instance iMon_mret_inst : MRet iMon := { mret a := Ret }.

  Fixpoint iMon_bind {a b : Type} (ma : iMon a) (f : a -> iMon b) :=
    match ma with
    | Ret x => f x
    | Next oc k => Next oc (fun x => iMon_bind (k x) f) end.
  Global Instance iMon_mbind_inst : MBind iMon :=
    { mbind _ _ f x := iMon_bind x f}.

  Fixpoint iMon_fmap {a b : Type} (ma : iMon a) (f : a -> b) :=
    match ma with
    | Ret x => Ret (f x)
    | Next oc k => Next oc (fun x => iMon_fmap (k x) f)
    end.
  Global Instance iMon_fmap_inst : FMap iMon :=
    { fmap _ _  f x := iMon_fmap x f}.






  (********** Instruction semantics and traces **********)

  (** The semantics of an complete instruction. A full definition of instruction
      semantics is allowed to have an internal state that gets passed from one
      instruction to the next. This is useful to handle pre-computed instruction
      semantics (e.g. Isla). For complete instruction semantics, we expect that
      A will be unit.*)
  Record iSem :=
    {
      (** The instruction model internal state *)
      isa_state : Type;
      (** The instruction model initial state for a thread with a specific Tid
          *)
      init_state : nat -> isa_state;
      semantic : isa_state -> iMon isa_state
    }.

  (** A single event in an instruction execution. As implied by the definition
      events cannot contain termination outcome (outcomes of type
      `outcome False`) *)
  Inductive iEvent :=
  | IEvent {T : Type} : outcome T -> T -> iEvent.

  (** An execution trace for a single instruction.
      If the result is an A, it means a successful execution that returned A
      If the result is a string, it means a GenericFail *)
  Definition iTrace (A : Type) : Type := list iEvent * (A + string).

  (** A trace is pure if it only contains external events. That means it must not
      contain control-flow event. The name "pure" is WIP.*)
  Fixpoint pure_iTrace_aux (tr : list iEvent) : Prop :=
    match tr with
    | (IEvent (Choose _) _) :: _ => False
    | _ :: t => pure_iTrace_aux t
    | [] => True
    end.
  Definition pure_iTrace {A : Type} (tr : iTrace A) :=
    let '(t,r) := tr in pure_iTrace_aux t.

  (** Definition of a trace semantics matching a trace. A trace is allowed to
      omit control-flow outcomes such as Choose and still be considered
      matching. *)
  Inductive iTrace_match {A : Type} : iMon A -> iTrace A -> Prop :=
  | TMNext T (oc : outcome T) (f : T -> iMon A) (obj : T) tl res :
    iTrace_match (f obj) (tl, res) ->
    iTrace_match (Next oc f) ((IEvent oc obj) :: tl, res)
  | TMChoose ty f (v : choose_type ty) tr :
    iTrace_match (f v) tr -> iTrace_match (Next (Choose ty) f) tr
  | TMSuccess a : iTrace_match (Ret a) ([], inl a)
  | TMFailure f s : iTrace_match (Next (GenericFail s) f) ([], inr s).

  (** Semantic equivalence for instructions *)
  Definition iMon_equiv `{Equiv A} (i1 i2 : iMon A) : Prop :=
    forall trace : iTrace A,
    pure_iTrace trace -> (iTrace_match i1 trace <-> iTrace_match i2 trace).

  End T.
  Arguments outcome : clear implicits.
  Arguments iMon : clear implicits.
  Arguments iSem : clear implicits.
  Arguments iTrace : clear implicits.
  Arguments iEvent : clear implicits.

  Definition iMonExtraMap (deps : Type) (out1 out2 : Type -> Type)
    := forall (A : Type), out1 A -> iMon deps out2 A.

  (** Suppose we can simulate the outcome of out1 in the instruction monad with
      architecture outcomes out2. Then  *)
  Fixpoint map_extra_iMon {deps : Type} {out1 out2 : Type -> Type} {B : Type}
    (f : iMonExtraMap deps out1 out2) (mon : iMon deps out1 B) :
    iMon deps out2 B :=
    match mon in iMon _ _ _ return iMon deps out2 _ with
    | Ret b => Ret b
    | Next oc k0 =>
        let k := fun x => map_extra_iMon f (k0 x) in
        match oc in outcome _ _ T
              return (T -> iMon deps out2 B) -> iMon deps out2 B with
        | RegRead reg direct => Next (RegRead reg direct)
        | RegWrite reg direct deps val =>
            Next (RegWrite reg direct deps val)
        | MemRead n readreq => Next (MemRead n readreq)
        | MemWrite n writereq => Next (MemWrite n writereq)
        | InstrAnnounce opcode => Next (InstrAnnounce opcode)
        | BranchAnnounce sz pa deps => Next (BranchAnnounce sz pa deps)
        | Barrier barrier => Next (Barrier barrier)
        | CacheOp deps cache_op => Next (CacheOp deps cache_op)
        | TlbOp deps tlb_op => Next (TlbOp deps tlb_op)
        | TakeException fault => Next (TakeException fault)
        | ReturnException pa => Next (ReturnException pa)
        | ExtraOutcome aout => iMon_bind (f _ aout)
        | GenericFail msg => Next (GenericFail msg)
        | CycleCount => Next CycleCount
        | GetCycleCount => Next GetCycleCount
        | Choose n => Next (Choose n)
        | Discard => Next (Discard)
        end k
    end.

End Interface.

Module Type InterfaceT (A : Arch).
  Include Interface A.
End InterfaceT.

Module Type InterfaceWithArch.
  Declare Module Arch : Arch.
  Include Arch.
  Include Interface Arch.
End InterfaceWithArch.
