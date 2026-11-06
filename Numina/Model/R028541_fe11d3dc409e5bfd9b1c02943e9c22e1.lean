import Mathlib

open Real Set
open scoped BigOperators



noncomputable def solution_9294 := λ (x : {x : ℝ // x > 4}) => -√x

noncomputable def f_9294 := λ (x : {x : ℝ // x < -2}) => (x : ℝ)^2

lemma hsolution : ∀ x, solution_9294 x < -2 := by
  intro x; dsimp [solution_9294]
  obtain ⟨x, hx⟩ := x
  simp_all
  have : √x^2 = x := Real.sq_sqrt (by linarith)
  have hxpos : 0 < x := by linarith
  rw [← this, (show (4 : ℝ) = 2 ^ 2 by ring)] at hx
  have : |2| < |√x| := sq_lt_sq.mp (GT.gt.lt hx)
  simp_all
  rw [abs_of_nonneg <| Real.sqrt_nonneg x] at this
  exact this

lemma hf : ∀ x, f_9294 x > 4 := by
  intro x; dsimp [f_9294]
  obtain ⟨x, hx⟩ := x; simp_all
  rw [(show (4 : ℝ) = 2 ^ 2 by linarith), sq_lt_sq]
  simp_all
  have : 2 < -x := by linarith
  rw [← abs_of_neg (show x < 0 by linarith)] at this
  exact this

theorem algebra_9294
  : (∀ x, f_9294 ⟨solution_9294 x, hsolution x⟩ = x) ∧ ∀ x, solution_9294 ⟨f_9294 x, hf x⟩ = x := by 
  have h1 : ∀ x : { x : ℝ // x > 4 }, f_9294 ⟨solution_9294 x, hsolution x⟩ = ↑x := by 
    intro x
    obtain ⟨x_val, hx⟩ := x 
    simp_all [f_9294, solution_9294] 
    have hx_pos : 0 < x_val := by linarith 
    have h7 : (√x_val) ^ 2 = x_val := by 
      have hx_nonneg : 0 ≤ x_val := by linarith
      exact Real.sq_sqrt hx_nonneg 
    norm_num at h7 ⊢ 
    <;> nlinarith 
  have h2 : ∀ x : { x : ℝ // x < -2 }, solution_9294 ⟨f_9294 x, hf x⟩ = x := by
    intro x 
    obtain ⟨x_val, hx⟩ := x 
    simp_all [solution_9294, f_9294] 
    <;> try { 
      have hx2' : x_val < -2 := by exact_mod_cast hx 
      have hx1 : x_val < 0 := by linarith 
      have h3 : √((x_val : ℝ) ^ 2) = - (x_val : ℝ) := by 
        rw [Real.sqrt_sq_eq_abs] 
        rw [abs_of_neg hx1]
      norm_num at h3 ⊢ 
      <;> nlinarith 
    }
  constructor 
  · exact h1 
  · exact h2