import Mathlib

open Finset

theorem algebra_39765 {f : ℕ → ℤ}
    (hf : ∀ n, f n = ∑ i ∈ Icc 1 n, Nat.factorial i) :
    ∃ P Q : Polynomial ℤ, ∀ n ≥ 1, f (n + 2) = P.eval (n : ℤ) * f (n + 1) + Q.eval (n : ℤ) * f n := by 
  use (Polynomial.X + 3)
  use (-Polynomial.X - 2)
  intro n hn
  rw [hf (n + 2), hf (n + 1), hf n]
  simp at *
  <;> try { 
    simp [sum_Icc_succ_top, Nat.factorial] at *
    <;> ring_nf
    <;> norm_num
    <;> try { 
      simp [Nat.factorial] at *
      <;> ring
    }
    <;> try { 
      simp [Nat.cast_add, Nat.cast_mul, Nat.cast_pow] 
    }
    <;> try { 
      have h1 : n ≥ 1 := by linarith
      have h2 : n + 1 ≥ 2 := by omega 
      have h3 : n + 2 ≥ 3 := by omega 
      cases n with 
      | zero => linarith 
      | succ n => 
        simp_all [sum_Icc_succ_top, Nat.factorial] 
        <;> ring_nf 
        <;> norm_num 
        <;> omega 
    }
  }
  <;> try { 
    cases n with
    | zero => linarith 
    | succ n => 
      simp_all [sum_Icc_succ_top, Nat.factorial] 
      <;> ring_nf 
      <;> norm_num 
      <;> omega 
  }