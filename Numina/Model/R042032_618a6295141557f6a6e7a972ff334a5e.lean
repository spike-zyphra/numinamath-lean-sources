import Mathlib
open Finset Complex

theorem number_theory_97893 (z m : Nat -> Complex) (h0:z 0= -20+20*I) (hm:∀ n,m n=I^n*(n+1)) (hz :∀(n:Nat), z (n+1)=z n +m n):
    z 2020=-1030-990*I:=by
  have h1 : ∀ k : Nat, z (4 * k) = -20 - (k : ℂ) * (2 : ℂ) + (20 - (k : ℂ) * (2 : ℂ)) * I := by
    intro k
    induction k with
    | zero => 
      simp [h0]
      <;> norm_num [Complex.ext_iff]
      <;> ring_nf <;> norm_num
    | succ k ih => 
      have h2 : z (4 * (k + 1)) = z (4 * k + 4) := by ring_nf
      rw [h2]
      have eq1 : z (4 * k + 1) = z (4 * k) + m (4 * k) := hz (4 * k)
      have eq2 : z (4 * k + 2) = z (4 * k + 1) + m (4 * k + 1) := hz (4 * k + 1)
      have eq3 : z (4 * k + 3) = z (4 * k + 2) + m (4 * k + 2) := hz (4 * k + 2)
      have eq4 : z (4 * k + 4) = z (4 * k + 3) + m (4 * k + 3) := hz (4 * k + 3)
      rw [eq4, eq3, eq2, eq1]
      simp [hm, pow_succ, mul_add, pow_mul, ih]
      field_simp [Complex.ext_iff]
      ring_nf
      <;> simp [Complex.I_sq, Complex.I_mul_I] 
      <;> ring_nf <;> norm_num
      all_goals ring_nf
      all_goals norm_num
  have h2020 : (2020 : Nat) = 4 * (505 : Nat) := by norm_num
  rw [h2020]
  specialize h1 505
  rw [h1]
  norm_num [Complex.ext_iff]
  <;> ring_nf <;> norm_num
  all_goals ring_nf
  all_goals norm_num
  all_goals ring_nf
  all_goals norm_num
  all_goals ring_nf
  all_goals norm_num
  all_goals ring_nf
  all_goals norm_num