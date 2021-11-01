Require Import BBST.Axiom.Meta.
Require Import BBST.Axiom.Separation.
Require Import BBST.Axiom.Pairing.
Require Import BBST.Definition.Emptyset.
Require Import BBST.Definition.OneTwo.

(* 
   建模并验证罗素悖论的一种错误形式:
   A = { x | x ∉ A }
*)

Theorem 逆否命题: ∀p q:Prop, (p → q) → ¬q → ¬p.
Proof. tauto. Qed.

(*
    集合函数的Y组合子，支持递归定义的集合，用来定义 A = { x | x ∉ A } 
*)
Axiom Y: (集合 -> 集合) -> 集合.
Axiom 递归公理: forall P:集合 -> 集合, Y P = P (Y P).

Definition 伪罗素集 := Y (λ B, { x ∊ 壹 | x ∉ B }).

Lemma 伪罗素集引理: ∀x ∈ 壹, (x ∈ 伪罗素集 ↔ x ∉ 伪罗素集).
Proof.
    intros. split; intros H1.
    - unfold 伪罗素集 in H1. rewrite 递归公理 in H1. 
      now apply 分离之条件 in H1.
    - unfold 伪罗素集. rewrite 递归公理. now apply 分离介入.  
Qed.

Lemma 伪罗素集引理二: ∀x ∈ 壹, ¬¬(x ∈ 伪罗素集).
Proof.
    intros. intros H1. 
    destruct (伪罗素集引理 x H) as [H2 H3]. auto.
Qed.

Lemma 伪罗素集引理三: ∀x ∈ 壹, ¬(x ∉ 伪罗素集) → x ∉ 伪罗素集.
Proof.
    intros x H. apply 逆否命题. 
    destruct (伪罗素集引理 x H) as [H2 H3]. auto.
Qed.

(* 这个定理说明，递归公理和ZFC公理系统是不相容的 *)
Theorem 伪罗素悖论: False.
Proof.
    assert (∀x ∈ 壹, False).
    { intros. assert (x ∉ 伪罗素集). 
        { apply 伪罗素集引理三. easy.
          now apply 伪罗素集引理二. }
      apply H0. destruct (伪罗素集引理 x H) as [H2 H3]. 
      now apply H3. }
    apply (H ∅). apply 壹介入.
Qed.

Print Assumptions 伪罗素悖论.
