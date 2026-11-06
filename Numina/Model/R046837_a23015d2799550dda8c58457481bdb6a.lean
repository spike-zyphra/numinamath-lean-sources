import Mathlib

open Polynomial

theorem algebra_14909 {p : Polynomial ℂ} (hp : p.Monic)
    (hcoef : ∀ i, (p.coeff i).im = 0)
    (h1 : p.eval (3 - 2 * Complex.I) = 0) (h2 : p.eval 0 = -52)
    (h_cubic : p.degree = 3) :
    p = X ^ 3 - 10 * X ^ 2 + 37 * X - 52 := by
  have h3 : p.natDegree = 3 := by
    rw [natDegree_eq_of_degree_eq_some h_cubic]
    all_goals try simp
  -- Compute p(x) explicitly using coefficients
  have eq5 : p.coeff 0 = -52 := by
    have eq3 : p.eval (0 : ℂ) = p.coeff 0 := by
      simp [Polynomial.eval_eq_sum_range, h3, Finset.sum_range_succ]
      <;> ring_nf <;> simp [Complex.ext_iff]
      all_goals try ring_nf
      all_goals try simp [h3]
    rw [eq3] at h2
    exact_mod_cast h2
  -- Compute p(x) evaluated at 3-2i =0 gives coeff equations
  have eq6 : p.eval (3 - 2 * Complex.I) =
      p.coeff 0 + p.coeff 1 * (3 - 2 * Complex.I) + p.coeff 2 * (3 - 2 * Complex.I) ^ 2 + p.coeff 3 * (3 - 2 * Complex.I) ^ 3 := by 
    simp [Polynomial.eval_eq_sum_range, h3, Finset.sum_range_succ]
    <;> ring_nf 
    <;> norm_num [pow_two, pow_succ]
    all_goals try simp [h3]
  rw [eq6] at h1
  have eq7 : (3 - 2 * Complex.I) ^ 2 = 5 - 12 * Complex.I := by
    calc
      (3 - 2 * Complex.I) ^ 2
          = (3 - 2 * Complex.I) * (3 - 2 * Complex.I) := by ring
      _ = 9 - 6 * Complex.I - 6 * Complex.I + 4 * (Complex.I * Complex.I) := by ring_nf
      _ = 9 - 6 * Complex.I - 6 * Complex.I + 4 * (-1) := by simp [Complex.I_mul_I]
      _ = 5 - 12 * Complex.I := by ring_nf
  have eq8 : (3 - 2 * Complex.I) ^ 3 = -9 - 46 * Complex.I := by 
    calc
      (3 - 2 * Complex.I) ^ 3
          = (3 - 2 * Complex.I) * ((3 - 2 * Complex.I) ^ 2) := by ring
      _ = (3 - 2 * Complex.I) * (5 - 12 * Complex.I) := by rw [eq7]
      _ = 15 - 36 * Complex.I - 10 * Complex.I + 24 * (Complex.I * Complex.I) := by ring_nf
      _ = 15 - 36 * Complex.I - 10 * Complex.I + 24 * (-1) := by simp [Complex.I_mul_I]
      _ = -9 - 46 * Complex.I := by ring_nf
  -- Simplify h1 using computed powers and equate real and complex parts
  rw [eq7, eq8] at h1 
  -- Monic gives leading coefficient 1: p.coeff 3 =1
  have eq9 : p.coeff 3 = 1 := by
    have h4 : p.leadingCoeff = 1 := by 
      simpa using hp
    have h5 : p.leadingCoeff = p.coeff (p.natDegree) := by
      rw [leadingCoeff]
      <;> simp
    rw [h5] at h4 
    rw [show p.natDegree = 3 by exact h3] at h4
    exact_mod_cast h4
  -- Derive other coefficient values step by step
  have eq10 : p.coeff 1 = 37 := by
    simp [Complex.ext_iff, hcoef 1, hcoef 2, hcoef 3] at h1 eq5 eq9 ⊢
    norm_num at h1 eq5 eq9 ⊢
    ring_nf at h1 eq5 eq9 ⊢
    norm_num at h1 eq5 eq9 ⊢
    try { 
      nlinarith 
    }
    all_goals try { 
      linarith 
    }
  -- Derive coeff2
  have eq11 : p.coeff 2 = -10 := by
    simp [Complex.ext_iff, hcoef 1, hcoef 2, hcoef 3] at h1 eq5 eq9 ⊢
    norm_num at h1 eq5 eq9 ⊢
    ring_nf at h1 eq5 eq9 ⊢
    norm_num at h1 eq5 eq9 ⊢
    try { 
      nlinarith 
    }
    all_goals try { 
      linarith 
    }
  -- Show that p is equal to the desired polynomial.
  have eq6 : p = X ^ 3 - 10 * X ^ 2 + 37 * X - 52 := by
    apply Polynomial.funext
    intro x
    have eq4 : p.eval x = (-52 + 37 * x - 10 * x^2 + x^3) := by
      simp [Polynomial.eval_eq_sum_range, h3, Finset.sum_range_succ, eq5, eq10, eq11, eq9]
      <;> ring_nf
      <;> simp [Complex.ext_iff, h3, Finset.sum_range_succ]
      <;> ring_nf
      <;> try { 
        tauto 
      }
      all_goals try { 
        nlinarith 
      }
    simp [eq4, Complex.ext_iff]
    <;> ring_nf
    <;> norm_num [Complex.ext_iff]
    all_goals try { 
      tauto 
    }
    all_goals try { 
      nlinarith 
    }
  exact_mod_cast eq6