(* Simply Typed Lambda Calculus *)
(* Yuxiang Pan *)

Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Import ListNotations.

(* Type *)
Inductive tp : Set :=
    | tp_nat    : tp
    | tp_arr    : tp -> tp -> tp.

(* Terms with explicit substitution *)
Inductive tm : Set :=
    | tm_var    : nat -> tm
    | tm_zero   : tm
    | tm_succ   : tm -> tm
    | tm_lamb   : tm -> tm
    | tm_appl   : tm -> tm -> tm
    | tm_recc   : tm -> tm -> tm -> tm
    | tm_subs   : tm -> subs -> tm
with subs    : Set :=
    | s_id      : subs
    | s_weak    : subs
    | s_comp    : subs -> subs -> subs
    | s_extd    : subs -> tm -> subs.

Definition context := list tp.

Inductive weaken : context -> context -> Set :=
    | I : forall (ctx : context),
        weaken ctx ctx
    | P : forall (T : tp) (ctx1 : context) (ctx2 : context),
        weaken ctx1 ctx2 -> weaken (T :: ctx1) ctx2
    | Q : forall (T : tp) (ctx1 : context) (ctx2 : context),
        weaken ctx1 ctx2 -> weaken (T :: ctx1) (T :: ctx2).

(* Normal and neutral forms *)
Inductive nf : Set :=
    | N_ne      : ne -> nf
    | N_zero    : nf
    | N_succ    : nf -> nf
    | N_lamb    : nf -> nf
with ne      : Set :=
    | N_var     : nat -> ne
    | N_appl    : ne -> nf -> ne
    | N_recc    : nf -> nf -> ne -> ne.

Fixpoint Nf_to_tm (N : nf) : tm :=
    match N with
    | N_ne ne1           => Ne_to_tm ne1
    | N_zero             => tm_zero
    | N_succ nf1         => tm_succ (Nf_to_tm nf1)
    | N_lamb nf1         => tm_lamb (Nf_to_tm nf1)
    end
with Ne_to_tm (N : ne) : tm :=
    match N with
    | N_var n            => tm_var n
    | N_appl ne1 nf1     => tm_appl (Ne_to_tm ne1) (Nf_to_tm nf1)
    | N_recc nf1 nf2 ne1 => tm_recc (Nf_to_tm nf1) (Nf_to_tm nf2) (Ne_to_tm ne1)
    end.

(* Typing Rules *)
Inductive lookup : nat -> tp -> context -> Prop :=
    (* T is first in ctx so has index 0 *)
    | base : forall (T : tp) (ctx : context),
        lookup 0 T (T :: ctx)
    (* If T1 has index n in ctx then T1 has index S(n) in T2 :: ctx *)
    | step : forall (n : nat) (T1 : tp) (T2 : tp) (ctx : context),
        lookup n T1 ctx ->
        lookup (S n) T1 (T2 :: ctx).

(* Page 24 of habil *)
Inductive tm_rule : context -> tm -> tp -> Prop :=
    (* If T is in ctx with index x then we can introduce it as variable x of type T from ctx*)
    | lookup_tm  : forall (x : nat) (T : tp) (ctx : context),
        lookup x T ctx ->
        tm_rule ctx (tm_var x) T
    | zero_intro : forall (ctx : context),
        tm_rule ctx tm_zero tp_nat
    | succ_intro : forall (n : tm) (ctx : context),
        tm_rule ctx n tp_nat ->
        tm_rule ctx (tm_succ n) tp_nat
    | lamb_intro : forall (t : tm) (T1 : tp) (T2 : tp) (ctx : context),
        tm_rule (T1 :: ctx) t T2 ->
        tm_rule ctx (tm_lamb t) (tp_arr T1 T2)
    | lamb_elim  : forall (t1 : tm) (t2 : tm) (T1 : tp) (T2 : tp) (ctx : context),
        tm_rule ctx t1 (tp_arr T1 T2) ->
        tm_rule ctx t2 T1             ->
        tm_rule ctx (tm_appl t1 t2) T2
    | recc_intro : forall (tz : tm) (ts : tm) (tn : tm) (T : tp) (ctx : context),
        tm_rule ctx tz T                            ->
        tm_rule ctx ts (tp_arr tp_nat (tp_arr T T)) ->
        tm_rule ctx tn tp_nat                       ->
        tm_rule ctx (tm_recc tz ts tn) T
    | subs_term  : forall (sigma : subs) (t : tm) (T : tp) (ctx1 : context) (ctx2 : context),
        tm_rule ctx1 t T          ->
        subs_rule ctx2 sigma ctx1 ->
        tm_rule ctx2 (tm_subs t sigma) T
with subs_rule : context -> subs -> context -> Prop :=
    | rule_id   : forall (ctx : context),
        subs_rule ctx s_id ctx
    | rule_weak : forall (T : tp) (ctx : context),
        subs_rule (T :: ctx) s_weak ctx
    | rule_comp : forall (sigma1 : subs) (sigma2 : subs) (ctx1 : context) (ctx2 : context) (ctx3 : context),
        subs_rule ctx1 sigma1 ctx2 ->
        subs_rule ctx2 sigma2 ctx3 ->
        subs_rule ctx1 (s_comp sigma2 sigma1) ctx3
    | rule_extd : forall (sigma : subs) (t : tm) (T : tp) (ctx1 : context) (ctx2 : context),
        subs_rule ctx1 sigma ctx2 ->
        tm_rule ctx1 t T          ->
        subs_rule ctx1 (s_extd sigma t) (T :: ctx2).

Inductive tm_eq : context -> tm -> tm -> tp -> Prop :=
    (* Term equality *)
    | var_eq  : forall (n : nat) (T : tp) (ctx : context),
        lookup n T ctx ->
        tm_eq ctx (tm_var n) (tm_var n) T
    | zero_eq : forall (ctx : context),
        tm_eq ctx tm_zero tm_zero tp_nat
    | succ_eq : forall (n : tm) (ctx : context),
        tm_eq ctx n n tp_nat ->
        tm_eq ctx (tm_succ n) (tm_succ n) tp_nat
    | lamb_cong : forall (t1 : tm) (t2 : tm) (T1 : tp) (T2 : tp) (ctx : context),
        tm_eq (T1 :: ctx) t1 t2 T2 ->
        tm_eq ctx (tm_lamb t1) (tm_lamb t2) (tp_arr T1 T2)
    | appl_cong : forall (t11 : tm) (t12 : tm) (t21 : tm) (t22 : tm) (T1 : tp) (T2 : tp) (ctx : context),
        tm_eq ctx t11 t12 (tp_arr T1 T2) ->
        tm_eq ctx t21 t22 T1             ->
        tm_eq ctx (tm_appl t11 t21) (tm_appl t12 t22) T2
    | recc_cong : forall (tz1 : tm) (ts1 : tm) (tn1 : tm) (tz2 : tm) (ts2 : tm) (tn2 : tm)
                (T : tp) (ctx : context),
        tm_eq ctx tz1 tz2 T                            ->
        tm_eq ctx ts1 ts2 (tp_arr tp_nat (tp_arr T T)) ->
        tm_eq ctx tn1 tn2 tp_nat                       ->
        tm_eq ctx (tm_recc tz1 ts1 tn1) (tm_recc tz2 ts2 tn2) T
    | subs_cong : forall (sigma1 : subs) (sigma2 : subs) (t1 : tm) (t2 : tm) (T : tp)
                  (ctx1 : context) (ctx2 : context),
        subs_eq ctx1 sigma1 sigma2 ctx2 ->
        tm_eq ctx2 t1 t2 T              ->
        tm_eq ctx1 (tm_subs t1 sigma1) (tm_subs t2 sigma2) T
    (* Substituted term equality *)
    | subs_zero_eq : forall (sigma : subs) (ctx1 : context) (ctx2 : context),
        subs_rule ctx1 sigma ctx2 ->
        tm_eq ctx1 (tm_subs tm_zero sigma) tm_zero tp_nat
    | subs_succ_eq : forall (sigma : subs) (n : tm) (ctx1 : context) (ctx2 : context),
        subs_rule ctx1 sigma ctx2 ->
        tm_rule ctx2 n tp_nat     ->
        tm_eq ctx1 (tm_subs (tm_succ n) sigma) (tm_succ (tm_subs n sigma)) tp_nat
    | subs_lamb_eq : forall (sigma : subs) (t : tm) (T1 : tp) (T2 : tp) (ctx1 : context) (ctx2 : context),
        subs_rule ctx1 sigma ctx2 ->
        tm_rule (T1 :: ctx2) t T2 ->
        tm_eq ctx1 (tm_subs (tm_lamb t) sigma)
                   (tm_lamb (tm_subs t (s_extd (s_comp sigma s_weak) (tm_var 0)))) (tp_arr T1 T2)
    | subs_recc_eq : forall (sigma : subs) (tz : tm) (ts : tm) (tn : tm) (T : tp) (ctx1 : context) (ctx2 : context),
        subs_rule ctx1 sigma ctx2 ->
        tm_rule ctx2 tz T ->
        tm_rule ctx2 ts (tp_arr tp_nat (tp_arr T T)) ->
        tm_rule ctx2 tn tp_nat ->
        tm_eq ctx1 (tm_subs (tm_recc tz ts tn) sigma) 
            (tm_recc (tm_subs tz sigma) (tm_subs ts sigma) (tm_subs tn sigma)) T
    (* (lambda t) [sigma] = lambda (t [sigma]) *)
    (* subs_rule (T1 :: ctx1) (s_extd sigma (tm_var 0)) (T1 :: ctx2) *)
    (* Related to local soundness *)
    | subs_lamb_beta_eq : forall (t1 : tm) (t2 : tm) (T1 : tp) (T2 : tp) (ctx : context),
        tm_rule (T1 :: ctx) t1 T2 ->
        tm_rule ctx t2 T1         ->
        (* Eliminate an introduced lambda: f(t1) t2 = f(t1[t2])*)
        (* Apply f(t1) to t2 = substitute t1 to t2 in f() *)
        tm_eq ctx (tm_appl (tm_lamb t1) t2) (tm_subs t1 (s_extd s_id t2)) T2
    | subs_recc_beta_zero : forall (tz : tm) (ts : tm) (T : tp) (ctx : context),
        tm_rule ctx tz T                            ->
        tm_rule ctx ts (tp_arr tp_nat (tp_arr T T)) ->
        (* Eliminate base case into result tz *)
        (* Apply rec(tz ts tn) to zero = tz *)
        tm_eq ctx (tm_recc tz ts tm_zero) tz T
    (* ts SSO (ts SO (ts 0 tz)) *)
    | subs_recc_beta_succ : forall (tz : tm) (ts : tm) (n : tm) (T : tp) (ctx : context),
        tm_rule ctx tz T                            ->
        tm_rule ctx ts (tp_arr tp_nat (tp_arr T T)) ->
        tm_rule ctx n tp_nat                        ->
        (* Eliminate succ case is equal to build 1 more layer on n case using ts s(n) *)
        tm_eq ctx (tm_recc tz ts (tm_succ n)) (tm_appl (tm_appl ts n) (tm_recc tz ts n)) T
    (* Related to local completeness *)
    | subs_lamb_eta_eq  : forall (t : tm) (T1 : tp) (T2 : tp) (ctx : context),
        tm_rule ctx t (tp_arr T1 T2) ->
        (* Introduce an eiminated t *)
        tm_eq ctx t (tm_lamb (tm_appl (tm_subs t s_weak) (tm_var 0))) (tp_arr T1 T2)
    | subs_appl_eq : forall (sigma : subs) (t1 : tm) (t2 : tm) (T1 : tp) (T2 : tp)
                     (ctx1 : context) (ctx2 : context),
        subs_rule ctx1 sigma ctx2      ->
        tm_rule ctx2 t1 (tp_arr T1 T2) ->
        tm_rule ctx2 t2 T1             ->
        tm_eq ctx1 (tm_subs (tm_appl t1 t2) sigma) (tm_appl (tm_subs t1 sigma) (tm_subs t2 sigma)) T2
    | subs_lookup  : forall (n : nat) (T1 : tp) (T2 : tp) (ctx : context),
        lookup n T1 ctx ->
        tm_eq (T2 :: ctx) (tm_subs (tm_var n) s_weak) (tm_var (S n)) T1
    | subs_id_eq   : forall (t : tm) (T : tp) (ctx : context),
        tm_rule ctx t T ->
        tm_eq ctx t (tm_subs t s_id) T
    | subs_comp_eq : forall (sigma1 : subs) (sigma2 : subs) (t : tm) (T : tp)
                     (ctx1 : context) (ctx2 : context) (ctx3 : context),
        subs_rule ctx1 sigma1 ctx2 ->
        subs_rule ctx2 sigma2 ctx3 ->
        tm_rule ctx3 t T           ->
        tm_eq ctx1 (tm_subs (tm_subs t sigma2) sigma1) (tm_subs t (s_comp sigma2 sigma1)) T
    | subs_extd_zero_eq : forall (sigma : subs) (t : tm) (T : tp) (ctx1 : context) (ctx2 : context),
        subs_rule ctx1 sigma ctx2 ->
        tm_rule ctx1 t T          ->
        tm_eq ctx1 t (tm_subs (tm_var 0) (s_extd sigma t)) T
    | subs_extd_succ_eq : forall (sigma : subs) (n : nat) (t : tm) (T : tp) (ctx1 : context) (ctx2 : context),
        subs_rule ctx1 sigma ctx2 ->
        tm_rule ctx1 t T          ->
        lookup n T ctx2           ->
        tm_eq ctx1 (tm_subs (tm_var n) sigma) (tm_subs (tm_var (S n)) (s_extd sigma t)) T
    (* Symmetry and transitivity *)
    | tm_symm : forall (t1 : tm) (t2 : tm) (T : tp) (ctx : context),
        tm_eq ctx t1 t2 T ->
        tm_eq ctx t2 t1 T
    | tm_tran : forall (t1 : tm) (t2 : tm) (t3 : tm) (T : tp) (ctx : context),
        tm_eq ctx t1 t2 T ->
        tm_eq ctx t2 t3 T ->
        tm_eq ctx t1 t3 T
    (* Substitution equality *)
with subs_eq : context -> subs -> subs -> context -> Prop :=
    | id_eq   : forall (ctx : context),
        subs_eq ctx s_id s_id ctx
    | weak_eq : forall (T : tp) (ctx : context),
        subs_eq (T :: ctx) s_weak s_weak ctx
    | comp_eq : forall (sigma1 : subs) (sigma2 : subs) (tau1 : subs) (tau2 : subs)
                (ctx1 : context) (ctx2 : context) (ctx3 : context),
        subs_eq ctx1 sigma1 sigma2 ctx2 ->
        subs_eq ctx2 tau1 tau2 ctx3     ->
        subs_eq ctx1 (s_comp tau1 sigma1) (s_comp tau2 sigma2) ctx3
    | extd_eq : forall (sigma1 : subs) (sigma2 : subs) (t1 : tm) (t2 : tm) (T : tp)
                (ctx1 : context) (ctx2 : context),
        subs_eq ctx1 sigma1 sigma2 ctx2 ->
        tm_eq ctx1 t1 t2 T              ->
        subs_eq ctx1 (s_extd sigma1 t1) (s_extd sigma2 t2) (T :: ctx2)
    | weak_extd_eq : forall (sigma : subs) (t : tm) (T : tp) (ctx1 : context) (ctx2 : context),
        subs_rule ctx1 sigma ctx2 ->
        tm_rule ctx1 t T          ->
        subs_eq ctx1 sigma (s_comp s_weak (s_extd sigma t)) ctx2
    | id_comp_l_eq : forall (sigma : subs) (ctx1 : context) (ctx2 : context),
        subs_rule ctx1 sigma ctx2 ->
        subs_eq ctx1 sigma (s_comp s_id sigma) ctx2
    | id_comp_r_eq : forall (sigma : subs) (ctx1 : context) (ctx2 : context),
        subs_rule ctx1 sigma ctx2 ->
        subs_eq ctx1 sigma (s_comp sigma s_id) ctx2
    | comp_assc_eq : forall (sigma1 : subs) (sigma2 : subs) (sigma3 : subs)
                     (ctx1 : context) (ctx2 : context) (ctx3 : context) (ctx4 : context),
        subs_rule ctx2 sigma1 ctx1 ->
        subs_rule ctx3 sigma2 ctx2 ->
        subs_rule ctx4 sigma3 ctx3 ->
        subs_eq ctx4 (s_comp sigma1 (s_comp sigma2 sigma3)) (s_comp (s_comp sigma1 sigma2) sigma3) ctx1
    | extd_var_eq  : forall (sigma : subs) (T : tp) (ctx1 : context) (ctx2 : context),
        subs_rule ctx1 sigma (T :: ctx2) ->
        subs_eq ctx1 sigma (s_extd (s_comp s_weak sigma) (tm_subs (tm_var 0) sigma)) (T :: ctx2)
    | subs_symm    : forall (sigma1 : subs) (sigma2 : subs) (ctx1 : context) (ctx2 : context),
        subs_eq ctx1 sigma1 sigma2 ctx2 ->
        subs_eq ctx1 sigma2 sigma1 ctx2
    | subs_tran    : forall (sigma1 : subs) (sigma2 : subs) (sigma3 : subs)
                     (ctx1 : context) (ctx2 : context),
        subs_eq ctx1 sigma1 sigma2 ctx2 ->
        subs_eq ctx1 sigma2 sigma3 ctx2 ->
        subs_eq ctx1 sigma1 sigma3 ctx2.

(* Exercise *)
Theorem tm_refl : forall (ctx : context) (t : tm) (T : tp),
    tm_rule ctx t T -> tm_eq ctx t t T
with subs_refl : forall (ctx1 : context) (ctx2 : context) (sigma : subs),
    subs_rule ctx1 sigma ctx2 -> subs_eq ctx1 sigma sigma ctx2.
Proof.
    - intros ctx t T. intros H. induction H.
        + apply var_eq. assumption.
        + apply zero_eq.
        + apply succ_eq. assumption.
        + apply lamb_cong. assumption.
        + eapply appl_cong; eassumption.
        + apply recc_cong; assumption.
        + eapply subs_cong.
            * apply subs_refl. eassumption.
            * assumption.
    - intros ctx1 ctx2 sigma H. induction H.
        + apply id_eq.
        + apply weak_eq.
        + eapply comp_eq; eassumption.
        + apply extd_eq.
            * assumption.
            * apply tm_refl. assumption.
Qed.

Theorem tm_pres : forall (ctx : context) (t : tm) (s : tm) (T : tp),
    tm_eq ctx t s T -> tm_rule ctx t T /\ tm_rule ctx s T
with subs_pres : forall (sigma : subs) (tau : subs) (ctx1 : context) (ctx2 : context),
    subs_eq ctx1 sigma tau ctx2 -> subs_rule ctx1 sigma ctx2 /\ subs_rule ctx1 tau ctx2.
Proof.
    - intros ctx t s T. intros H. induction H.
        + split; apply lookup_tm; assumption.
        + split; apply zero_intro.
        + destruct IHtm_eq; split; apply succ_intro; assumption.
        + destruct IHtm_eq; split; apply lamb_intro; assumption.
        + destruct IHtm_eq1; destruct IHtm_eq2; split; eapply lamb_elim; eassumption.
        + destruct IHtm_eq1; destruct IHtm_eq2; destruct IHtm_eq3; split; apply recc_intro; assumption.
        + destruct IHtm_eq; split; eapply subs_term; 
          try eassumption; 
          try (apply subs_pres in H; destruct H; assumption).
        + split. eapply subs_term. eapply zero_intro. eassumption. eapply zero_intro.
        + split. eapply subs_term. eapply succ_intro; eassumption. assumption.
          apply succ_intro. eapply subs_term; eassumption.
        + split. eapply subs_term. eapply lamb_intro. eassumption. assumption.
          apply lamb_intro. eapply subs_term. eassumption. apply rule_extd. eapply rule_comp.
          eapply rule_weak. assumption. apply lookup_tm. apply base.
        + split. eapply subs_term. eapply recc_intro; eassumption. assumption.
          apply recc_intro; eapply subs_term; eassumption.
        + split. eapply lamb_elim. 
          eapply lamb_intro; eassumption. 
          assumption.
          eapply subs_term. eassumption. apply rule_extd. apply rule_id. assumption.
        + split. apply recc_intro; try assumption. apply zero_intro. assumption.
        + split. apply recc_intro; try assumption.
          apply succ_intro; assumption.
          eapply lamb_elim. eapply lamb_elim; eassumption.
          apply recc_intro; assumption.
        + split. assumption.
          apply lamb_intro; eapply lamb_elim.
          eapply subs_term. eassumption. apply rule_weak. apply lookup_tm. apply base.
        + split. eapply subs_term.
          eapply lamb_elim; eassumption.
          assumption.
          eapply lamb_elim. eapply subs_term; eassumption.
          eapply subs_term; eassumption.
        + split. eapply subs_term. eapply lookup_tm; eassumption.
          apply rule_weak.
          apply lookup_tm; apply step; assumption.
        + split. assumption. 
          eapply subs_term. eassumption. eapply rule_id.
        + split; eapply subs_term.
          eapply subs_term; eassumption.
          assumption.
          eassumption.
          eapply rule_comp; eassumption.
        + split. assumption.
          eapply subs_term. eapply lookup_tm; eapply base.
          eapply rule_extd; eassumption.
        + split. eapply subs_term. eapply lookup_tm; eassumption.
          eassumption.
          eapply subs_term. eapply lookup_tm; eapply step; eassumption.
          eapply rule_extd; eassumption.
        + destruct IHtm_eq. split; assumption.
        + destruct IHtm_eq1. destruct IHtm_eq2. split; assumption.
    - intros sigma tau ctx1 ctx2. intros H. induction H.
        + split; apply rule_id.
        + split; apply rule_weak.
        + destruct IHsubs_eq1. destruct IHsubs_eq2. split; eapply rule_comp; eassumption.
        + destruct IHsubs_eq. apply tm_pres in H0. destruct H0. split; apply rule_extd; assumption.
        + split. assumption. eapply rule_comp.
          eapply rule_extd; eassumption.
          apply rule_weak.
        + split. assumption.
          eapply rule_comp. eassumption. apply rule_id.
        + split. assumption.
          eapply rule_comp. eapply rule_id. eassumption.
        + split; eapply rule_comp; try eapply rule_comp; eassumption.
        + split. eassumption. apply rule_extd.
          eapply rule_comp. eassumption. apply rule_weak.
          eapply subs_term. eapply lookup_tm; eapply base. eassumption.
        + destruct IHsubs_eq. split; assumption.
        + destruct IHsubs_eq1. destruct IHsubs_eq2. split; assumption.
Qed.

(* Domain *)
Inductive D : Type :=
    | D_zero : D
    | D_succ : D -> D
    | D_lamb : tm -> (nat -> D) -> D
    | D_updt : tp -> DNe -> D
with DNf : Type :=
    | D_down : tp -> D -> DNf
with DNe : Type :=
    | D_var  : nat -> DNe
    | D_appl : DNe -> DNf -> DNe
    | D_recc : DNf -> DNf -> DNe -> DNe.

Notation Env := (nat -> D).

Definition extend (p : Env) (d : D) (n : nat) : D :=
    match n with
    | 0    => d
    | S n' => p n'
    end.

Definition drop (p : Env) (n : nat) : D := p (S n).

Inductive tm_eval : tm -> Env -> D -> Prop :=
    | eval_var  : forall (t : tm) (p : Env) (x : nat),
        tm_eval (tm_var x) p (p x)
    | eval_zero : forall (p : Env),
        tm_eval tm_zero p D_zero
    | eval_succ : forall (t : tm) (p : Env) (d : D),
        tm_eval t p d ->
        tm_eval (tm_succ t) p (D_succ d)
    | eval_lamb : forall (t : tm) (p : Env),
        tm_eval (tm_lamb t) p (D_lamb t p)
    | eval_appl : forall (t1 : tm) (t2 : tm) (p : Env) (f : D) (d1 : D) (d2 : D),
        tm_eval t1 p f        ->
        tm_eval t2 p d1        ->
        appl_eval f d1 d2       ->
        tm_eval (tm_appl t1 t2) p d2
    | eval_recc : forall (tz : tm) (ts : tm) (tn : tm) (p : Env) (dz : D) (ds : D) (dn: D) (d : D),
        tm_eval tz p dz       ->
        tm_eval ts p ds       ->
        tm_eval tn p dn       ->
        recc_eval dz ds dn d  ->
        tm_eval (tm_recc tz ts tn) p d
    | eval_subs : forall (sigma : subs) (t : tm) (p1 : Env) (p2 : Env) (d : D),
        subs_eval sigma p1 p2 ->
        tm_eval t p2 d        ->
        tm_eval (tm_subs t sigma) p1 d
with appl_eval : D -> D -> D -> Prop :=
    | appl_eval_lamb : forall (t : tm) (p : Env) (d1 : D) (d2 : D),
        tm_eval t (extend p d1) d2 ->
        appl_eval (D_lamb t p) d1 d2
    | appl_eval_appl : forall (T1 : tp) (T2 : tp) (e : DNe) (d : D),
        appl_eval (D_updt (tp_arr T1 T2) e) d (D_updt T2 (D_appl e (D_down T1 d)))
with recc_eval : D -> D -> D -> D -> Prop :=
    | recc_eval_zero : forall (dz : D) (ds : D),
        recc_eval dz ds D_zero dz
    | recc_eval_succ : forall (dz : D) (ds : D) (dn : D) (a : D) (f : D) (b : D),
        recc_eval dz ds dn a ->
        appl_eval ds dn f    ->
        appl_eval f a b      ->
        recc_eval dz ds (D_succ dn) b
with subs_eval : subs -> Env -> Env -> Prop :=
    | subs_eval_id   : forall (p : Env),
        subs_eval s_id p p
    | subs_eval_weak : forall (p : Env),
        subs_eval s_weak p (drop p)
    | subs_eval_comp : forall (sigma1 : subs) (sigma2 : subs) (p1 : Env) (p2 : Env) (p3 : Env),
        subs_eval sigma1 p1 p2 ->
        subs_eval sigma2 p2 p3 ->
        subs_eval (s_comp sigma1 sigma2) p1 p3
    | subs_eval_extd : forall (sigma : subs) (t : tm) (p1 : Env) (p2 : Env) (d : D),
        subs_eval sigma p1 p2 ->
        tm_eval t p1 d        ->
        subs_eval (s_extd sigma t) p1 (extend p2 d).

Theorem tm_det : forall (t : tm) (p : Env) (a : D) (a' : D),
    tm_eval t p a  ->
    tm_eval t p a' ->
    a = a'
with appl_det : forall (f : D) (a : D) (b : D) (b' : D),
    appl_eval f a b  ->
    appl_eval f a b' ->
    b = b'
with recc_det : forall (dz : D) (ds : D) (dn : D) (d : D) (d' : D),
    recc_eval dz ds dn d  ->
    recc_eval dz ds dn d' ->
    d = d'
with subs_det : forall (sigma : subs) (p : Env) (p' : Env) (p'' : Env),
    subs_eval sigma p p'  ->
    subs_eval sigma p p'' ->
    p' = p''.
Proof.
    - intros t p a a'. intros H H'. inversion H; inversion H'; try congruence; subst.
        + inversion H5. rewrite H2 in H4; apply (tm_det _ _ d d0) in H4; congruence.
        + inversion H9. rewrite H4 in H6; rewrite H5 in H7;
          apply (tm_det _ _ f f0) in H0; apply (tm_det _ _ d1 d0) in H1; 
          try congruence.
          rewrite H0 in H2; apply (appl_det _ _ a a') in H2; congruence.
        + inversion H11. rewrite H5 in H7; rewrite H6 in H8; rewrite H12 in H9;
          apply (tm_det _ _ dz dz0) in H0; apply (tm_det _ _ ds ds0) in H1; apply (tm_det _ _ dn dn0) in H2;
          try congruence.
          rewrite H0 in H3; rewrite H1 in H3; rewrite H2 in H3;
          apply (recc_det _ _ _ a a') in H3; congruence.
        + inversion H7. apply (subs_det _ _ p2 p3) in H0; try congruence;
          rewrite H3 in H6; rewrite H0 in H1;
          apply (tm_det _ _ a a') in H1; congruence.
    - intros f a b b'. intros H H'. inversion H; inversion H'; try congruence; subst;
        inversion H5; rewrite H2 in H4; rewrite H3 in H4;
        apply (tm_det _ _ b b') in H0; congruence.
    - intros dz ds dn d d'. intros H H'. inversion H; inversion H'; subst.
        + reflexivity.
        + inversion H9. 
        + inversion H9.
        + inversion H12. rewrite H4 in H7; rewrite H4 in H8;
          apply (recc_det _ _ _ a a0) in H0; apply (appl_det _ _ f f0) in H1;
          try congruence.
          rewrite H0 in H2; rewrite H1 in H2;
          apply (appl_det _ _ d d') in H2; congruence.
    - intros sigma p p' p''. intros H H'. inversion H; inversion H'; try congruence; subst.
        + inversion H7. rewrite H3 in H5; rewrite H4 in H6;
          apply (subs_det _ _ p2 p4) in H0; try congruence.
          rewrite H0 in H1; apply (subs_det _ _ p' p'') in H1; congruence.
        + inversion H7. rewrite H3 in H5; rewrite H4 in H6;
          apply (subs_det _ _ p2 p3) in H0; apply (tm_det _ _ d d0) in H1; congruence.
Qed.

Inductive rf_eval : nat -> DNf -> nf -> Prop :=
    | R_zero : forall (n : nat),
        rf_eval n (D_down tp_nat D_zero) N_zero
    | R_succ : forall (n : nat) (d : D) (v : nf),
        rf_eval n (D_down tp_nat d) v ->
        rf_eval n (D_down tp_nat (D_succ d)) (N_succ v)
    | R_lamb : forall (n : nat) (f : D) (a : D) (M : tp) (T : tp) (w : nf),
        appl_eval f (D_updt M (D_var n)) a ->
        rf_eval (S n) (D_down T a) w       ->
        rf_eval n (D_down (tp_arr M T) f) (N_lamb w)
    | R_neut : forall (n : nat) (T : tp) (e : DNe) (u : ne),
        re_eval n e u ->
        rf_eval n (D_down tp_nat (D_updt T e)) (N_ne u)
with re_eval : nat -> DNe -> ne -> Prop :=
    | R_var : forall (n : nat) (x : nat),
        re_eval n (D_var x) (N_var (n - x - 1))
    | R_appl : forall (n : nat) (d : DNf) (e : DNe) (w : nf) (u : ne),
        re_eval n e u ->
        rf_eval n d w ->
        re_eval n (D_appl e d) (N_appl u w)
    | R_recc : forall (n : nat) (dz : DNf) (ds : DNf) (e : DNe) (vz : nf) (vs : nf) (u : ne),
        rf_eval n dz vz ->
        rf_eval n ds vs ->
        re_eval n e u   ->
        re_eval n (D_recc dz ds e) (N_recc vz vs u).

Theorem rf_det : forall (n : nat) (d : DNf) (w : nf) (w' : nf),
    rf_eval n d w  ->
    rf_eval n d w' ->
    w = w'
with re_det : forall (n : nat) (d : DNe) (u : ne) (u' : ne),
    re_eval n d u  ->
    re_eval n d u' ->
    u = u'.
Proof.
    - intros n d w w'. intros H H'. inversion H; inversion H'; try congruence; subst.
        + inversion H6. rewrite <- H2 in H0. apply (rf_det _ _ v v0) in H0.
            * rewrite H0. reflexivity.
            * assumption.
        + inversion H8. rewrite <- H7 in H0. rewrite <- H3 in H0.
          apply (appl_det _ _ a a0) in H0.
          rewrite <- H4 in H1. rewrite -> H0 in H1.
          apply (rf_det _ _ w0 w1) in H1.
            * rewrite H1. reflexivity.
            * assumption.
            * assumption.
        + inversion H6. rewrite H3 in H4. apply (re_det _ _ u u0) in H0.
            * rewrite H0. reflexivity.
            * assumption.
    - intros n d u u'. intros H H'. inversion H; inversion H'; try congruence; subst.
        + inversion H8. rewrite H3 in H5; rewrite H4 in H6; 
          apply (re_det _ _ u0 u1) in H0; apply (rf_det _ _ w w0) in H1; 
          congruence.
        + inversion H10. rewrite H4 in H6; rewrite H5 in H7; rewrite H9 in H8;
          apply (rf_det _ _ vz vz0) in H0; apply (rf_det _ _ vs vs0) in H1; apply (re_det _ _ u0 u1) in H2;
          congruence.
Qed.

Inductive Top : DNf -> DNf -> Prop :=
    | top : forall (d d' : DNf),
        (forall n, exists w, rf_eval n d w /\ rf_eval n d' w) ->
        Top d d'.

Inductive Bot : DNe -> DNe -> Prop :=
    | bot : forall (e e' : DNe),
        (forall n, exists u, re_eval n e u /\ re_eval n e' u) ->
        Bot e e'.

Lemma var_in_bot : forall (x : nat),
    Bot (D_var x) (D_var x).
Proof.
    intros x. econstructor; econstructor; econstructor; econstructor.
Qed.

Lemma appl_in_bot : forall (d d' : DNf) (e e' : DNe),
    Bot e e' ->
    Top d d' ->
    Bot (D_appl e d) (D_appl e' d').
Proof.
    intros d d' e e'. intros H H'. destruct H. destruct H'.
    apply bot. intros. destruct (H n). destruct (H0 n). exists (N_appl x x0).
    destruct H1. destruct H2. 
    split; econstructor; assumption.
Qed.

Lemma recc_in_bot : forall (dz dz' ds ds' : DNf) (dn dn' : DNe),
    Top dz dz' ->
    Top ds ds' ->
    Bot dn dn' ->
    Bot (D_recc dz ds dn) (D_recc dz' ds' dn').
Proof.
    intros dz dz' ds ds' dn dn'. intros Hz Hs Hn. destruct Hz. destruct Hs. destruct Hn.
    apply bot. intros. destruct (H n). destruct (H0 n). destruct (H1 n). exists (N_recc x x0 x1).
    destruct H2. destruct H3. destruct H4.
    split; econstructor; assumption.
Qed.

Lemma zero_in_top :
    Top (D_down tp_nat D_zero) (D_down tp_nat D_zero).
Proof.
    apply top. intro. exists N_zero. split; econstructor.
Qed.

Lemma succ_in_top : forall (n m : D),
    Top (D_down tp_nat n) (D_down tp_nat m) ->
    Top (D_down tp_nat (D_succ n)) (D_down tp_nat (D_succ m)).
Proof.
    intros n m. intros H. inversion H. apply top. intro. destruct (H0 n0). exists (N_succ x).
    destruct H3. split; econstructor; assumption.
Qed.

Notation Tp := (D -> D -> Prop).

Lemma bot_trans : forall (e e' e'' : DNe),
    Bot e e' -> Bot e' e'' -> Bot e e''.
Proof.
    intros e e' e''. intros H H0. induction H. inversion H0. apply bot. intro.
    destruct (H n). exists x. destruct H4. split. assumption. destruct (H1 n).
    destruct H6. apply (re_det n e' x x0) in H5; congruence.
Qed.

Inductive equiv_nat : Tp :=
    | zero_equiv : 
        equiv_nat D_zero D_zero
    | succ_equiv : forall (n m : D),
        equiv_nat n m ->
        equiv_nat (D_succ n) (D_succ m)
    | up_nat : forall (e e' : DNe),
        Bot e e' ->
        equiv_nat (D_updt tp_nat e) (D_updt tp_nat e').

Lemma nat_symm : forall (n m : D),
    equiv_nat n m -> equiv_nat m n.
Proof.
    intros n m. intros H. induction H.
    - apply zero_equiv.
    - apply succ_equiv. assumption.
    - apply up_nat. apply bot. intro. destruct H. destruct (H n). exists x. destruct H0.
      split; assumption.
Qed.

Lemma nat_trans : forall (n m l : D),
    equiv_nat n m -> equiv_nat m l -> equiv_nat n l.
Proof.
    intros n m l. intros H. generalize l. induction H; intros.
    - assumption.
    - inversion H0. subst. apply succ_equiv. auto.
    - inversion H0. subst. apply up_nat. apply (bot_trans e e' e'0); assumption.
Qed.

Inductive appl_equivalence_of_T : D -> D -> D -> D -> Tp -> Prop :=
    | appl_eq_of_T : forall (f f' a a' fa f'a' : D) (T : Tp),
        appl_eval f a fa     ->
        appl_eval f' a' f'a' ->
        T fa f'a' ->
        appl_equivalence_of_T f f' a a' T.

Inductive equiv_fun : Tp -> Tp -> D -> D -> Prop :=
    | func_equiv : forall (f f' : D) (M T : Tp),
        (forall a a', M a a' -> (appl_equivalence_of_T f f' a a' T)) ->
        equiv_fun M T f f'.

Fixpoint interp_type (T : tp) : Tp :=
    match T with
    | tp_nat     => equiv_nat
    | tp_arr M T => equiv_fun (interp_type M) (interp_type T)
    end.

Lemma interp_symm : forall (T : tp) (a b : D),
    interp_type T a b -> interp_type T b a.
Proof.
    intros T a b. intro H. dependent induction T; simpl.
    - apply nat_symm. destruct H; try econstructor; assumption.
    - simpl in H. destruct H. apply func_equiv. intros. 
      destruct (H a' a). auto. apply (appl_eq_of_T _ _ _ _ f'a' fa _); try assumption. auto.
Qed.

Lemma interp_trans : forall (T : tp) (a b c : D),
    interp_type T a b -> interp_type T b c -> interp_type T a c.
Proof.
    intros T a b c. intros H. dependent induction T.
    - intro. eapply nat_trans; eassumption.
    - intro. simpl in *. 
      apply func_equiv. intros.
      assert (H2 := interp_symm _ _ _ H1).
      assert (H3 := IHT1 _ _ _ H1 H2).
      assert (H4 := IHT1 _ _ _ H2 H1).
      dependent destruction H. dependent destruction H0.
      apply H in H1. apply H0 in H4.
      inversion H1. inversion H4. subst.
      assert (f'a' = fa0) by eauto using appl_det; subst.
      econstructor; eauto.
Qed.

Lemma interp_refl : forall (T : tp) (a b : D),
    interp_type T a b -> interp_type T a a.
Proof.
    intros T a b H. apply (interp_trans _ a b a) in H.
    - assumption.
    - apply interp_symm in H. assumption.
Qed.

Inductive equiv_rel : tp -> Tp -> Prop :=
    | rel : forall (T : tp) (A : Tp),
        (forall (e e' : DNe), Bot e e' -> A (D_updt T e) (D_updt T e')) ->
        (forall (a b : D), A a b -> Top (D_down T a) (D_down T b)) ->
        equiv_rel T A.

Lemma func_equiv_rel : forall (M U : tp) (A B : Tp),
    equiv_rel M A ->
    equiv_rel U B ->
    equiv_rel (tp_arr M U) (equiv_fun A B).
Proof.
    intros M U A B. intros H H0. constructor.
    - intros. apply func_equiv. intros. inversion H. inversion H0. subst. 
      apply (appl_eq_of_T _ _ _ _ (D_updt U (D_appl e (D_down M a))) (D_updt U (D_appl e' (D_down M a'))) _).
      apply appl_eval_appl.
      apply appl_eval_appl.
      apply H7. apply appl_in_bot. assumption. apply H4. assumption.
    - intros. inversion H. inversion H0. subst. apply top. intro.
      assert (H8 := var_in_bot n).
      apply H2 in H8.
      dependent destruction H1. apply H1 in H8. dependent destruction H8.
      apply H7 in H8. dependent destruction H8.
      destruct (H8 (S n)). destruct H9.
      econstructor. split; eapply R_lamb; eauto.
Qed.

Lemma nat_interp : equiv_rel tp_nat (interp_type tp_nat).
Proof.
    eapply rel; intros.
    - simpl. constructor. assumption.
    - intros. simpl in H. induction H.
        + apply zero_in_top.
        + apply succ_in_top. assumption.
        + dependent destruction H. constructor. intro. specialize (H n). destruct H. destruct H. 
          econstructor. split; econstructor; eassumption.
Qed.

Lemma type_interp : forall (T : tp),
    equiv_rel T (interp_type T).
Proof.
    intro T. dependent induction T.
    - apply nat_interp.
    - apply (func_equiv_rel _ _ _ _ IHT1 IHT2).
Qed.

Lemma interp_to_top : forall (T : tp),
    forall (a a' : D), interp_type T a a' -> Top (D_down T a) (D_down T a').
Proof.
    intros. assert (H0 := type_interp T). inversion H0. auto.
Qed.

Lemma bot_to_interp : forall (T : tp),
    forall (e e' : DNe), Bot e e' -> interp_type T (D_updt T e) (D_updt T e').
Proof.
    intros. assert (H0 := type_interp T). inversion H0. auto.
Qed.

Definition env_equiv (p p' : Env) (ctx : context) : Prop :=
    forall (x : nat) (T : tp), lookup x T ctx -> interp_type T (p x) (p' x).

Lemma env_equiv_symm : forall (p p' : Env) (ctx : context),
    env_equiv p p' ctx -> env_equiv p' p ctx.
Proof.
    intros p p' ctx. unfold env_equiv. intros. apply interp_symm. auto.
Qed.

Lemma env_equiv_refl : forall (p p' : Env) (ctx : context),
    env_equiv p p' ctx -> env_equiv p p ctx.
Proof.
    intros p p' ctx. unfold env_equiv. intros. apply (interp_refl _ _ (p' x)). auto.
Qed.

Lemma context_extension : forall (p p' : Env) (ctx : context) (a b : D) (T : tp),
    env_equiv p p' ctx ->
    interp_type T a b  ->
    env_equiv (extend p a) (extend p' b) (T :: ctx).
Proof.
    intros. unfold env_equiv. intros. induction x.
    - simpl. inversion H1. assumption.
    - simpl. inversion H1. subst. auto.
Qed.

Inductive interp_equiv (s t : tm) (p p' : Env) (T : tp) : Prop :=
    | ie :  forall (ds dt : D), 
            tm_eval s p ds  ->
            tm_eval t p' dt ->
            interp_type T ds dt ->
            interp_equiv s t p p' T.

Inductive interp_equiv_subs (sigma1 sigma2 : subs) (p p' : Env) (ctx : context) : Prop :=
    | ies : forall (p1 p2 : Env),
            subs_eval sigma1 p p1  ->
            subs_eval sigma2 p' p2 ->
            env_equiv p1 p2 ctx ->
            interp_equiv_subs sigma1 sigma2 p p' ctx.

Definition sem_tm_eq (ctx : context) (t t' : tm) (T : tp) : Prop :=
    forall (p p' : Env),
    env_equiv p p' ctx ->
    interp_equiv t t' p p' T.

Lemma tm_eq_symm : forall (ctx : context) (t t' : tm) (T : tp),
    sem_tm_eq ctx t t' T -> sem_tm_eq ctx t' t T.
Proof.
    intros ctx t t' T. unfold sem_tm_eq. intros. apply env_equiv_symm in H0.
    apply H in H0. inversion H0. apply (ie _ _ _ _ _ dt ds); auto. apply interp_symm. auto.
Qed.

Lemma tm_eq_trans : forall (ctx : context) (t t' t'' : tm) (T : tp),
    sem_tm_eq ctx t t' T -> sem_tm_eq ctx t' t'' T -> sem_tm_eq ctx t t'' T.
Proof.
    intros. unfold sem_tm_eq in *. intros. assert (H2 := H1).
    apply env_equiv_symm in H1. apply env_equiv_refl in H1. assert (H3 := H p p' H2).
    assert (H4 := H0 p' p' H1). inversion H3. inversion H4. apply (ie _ _ _ _ _ ds dt0); auto.
    assert (H11 := tm_det t' p' dt ds0 H6 H8). subst. 
    assert (H11 := interp_trans T ds ds0 dt0 H7 H10). auto.
Qed.

Fixpoint InitialEnv (ctx : context) (n : nat) : D :=
    match ctx, n with
    | nil, _ => D_zero
    | (T :: gamma), 0 => D_updt T (D_var (List.length gamma))
    | (T :: gamma), (S x) => InitialEnv gamma x
    end.

Lemma initial_refl : forall (ctx : context),
    env_equiv (InitialEnv ctx) (InitialEnv ctx) ctx.
Proof.
    intro. unfold env_equiv. intros. induction H.
    - simpl. apply bot_to_interp. apply var_in_bot.
    - simpl. assumption.
Qed.