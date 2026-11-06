import Mathlib
open Nat Real Finset Set
noncomputable section

-- Define a three-element set for constructing the non-associative example。
inductive S3 : Type
  | a : S3
  | b : S3
  | c : S3
deriving DecidableEq
open S3

/-33rd Putnam 1972 Problem A2 Let S be a set with a binary operation * such that (1) a * (a * b) = b for all a, b ∈ S, (2) (a * b) * b = a for all a, b ∈ S. Show that * is commutative. Give an example for which S is not associative.-/
theorem algebra_200123 {S : Type} (op : S → S → S)
  (h1 : ∀ a b : S, op a (op a b) = b)
  (h2 : ∀ a b : S, op (op a b) b = a) :
  (∀ a b : S, op a b = op b a) ∧
  ∃ (S' : Type) (op' : S' → S' → S'),
    (∀ a b : S', op' a (op' a b) = b) ∧
    (∀ a b : S', op' (op' a b) b = a) ∧
    (∃ a b c : S', op' (op' a b) c ≠ op' a (op' b c)) := by
  constructor
  -- Prove commutativity。
  · intro a b
    have h_step1 : op (op a b) (op (op a b) b) = op (op a b) a := by
      rw [h2]
    have h_step2 : op (op a b) (op (op a b) b) = b := by
      let c := op a b
      rw [h1 c b]
    have h_step3 : op (op a b) a = b := by
      rw [← h_step1, h_step2]
    have h_step4 : op (op (op a b) a) a = op b a := by
      rw [h_step3]
    have h_step5 : op (op (op a b) a) a = op a b := by
      rw [h2]
    have h_step6 : op b a = op a b := by
      rw [← h_step4, h_step5]
    exact h_step6.symm
  -- Construct a non-associative example。
  · -- Define the three-element set $S' = S3$ and operation $op'$.
    let S' := S3
    let op' : S3 → S3 → S3 := fun x y =>
      match x, y with
      | a, a => a
      | a, b => c
      | a, c => b
      | b, a => c
      | b, b => b
      | b, c => a
      | c, a => b
      | c, b => a
      | c, c => c
    use S', op'
    constructor
    -- Verify condition : $op' x (op' x y) = y$.
    · intro x y
      match x, y with
      | a, a => simp [op']
      | a, b => simp [op']
      | a, c => simp [op']
      | b, a => simp [op']
      | b, b => simp [op']
      | b, c => simp [op']
      | c, a => simp [op']
      | c, b => simp [op']
      | c, c => simp [op']
    constructor
    -- Verify condition : $op' (op' x y) y = x$.
    · intro x y
      match x, y with
      | a, a => simp [op']
      | a, b => simp [op']
      | a, c => simp [op']
      | b, a => simp [op']
      | b, b => simp [op']
      | b, c => simp [op']
      | c, a => simp [op']
      | c, b => simp [op']
      | c, c => simp [op']
    -- Prove non-associativity: $(op' (op' a a) b) ≠ op' a (op' a b)$.
    · use a, a, b
      have h_left : op' (op' a a) b = c := by simp [op']
      have h_right : op' a (op' a b) = b := by simp [op']
      have h_ne : c ≠ b := by
        intro h_eq
        injection h_eq
      exact h_ne
