import Mathlib
open Real

/-
Find the product of all real $x$ for which

$$
2^{3 x+1}-17 \cdot 2^{2 x}+2^{x+3}=0
$$
-/
theorem algebra_608406 (x:ℝ) : ((2:ℝ)^(3*x+1) - 17* 2 ^(2*x) + 2^(x+3) = 0) ↔ (x=3 ∨ x = -1) := by
  apply Iff.intro
  swap
  intro hx
  cases hx with
  | inl hx => 
    simp only [hx]
    norm_num
  | inr hx => 
    simp only [hx]
    norm_num
  intro h
  -- Let's rewrite the given equation in a form suitable for manipulation.
  have h1 : ((2:ℝ)^x) * (2* (2^x)^2 - 17* 2^x + 8) = 0 := by
    calc
      _ = (2:ℝ)^(3*x+1) - 17* 2 ^(2*x) + 2^(x+3) := by
        ring_nf
        have _1: (2:ℝ) ^ (1 + x*3) = (2^x) ^ 3 * 2 := by
          calc
            _ = (2:ℝ) ^ (x*3) * 2^1 := by 
              rw [rpow_add]; norm_num; linarith; norm_num
            _ = ((2:ℝ) ^x)^3 * 2^1 := by
              rw [rpow_mul]; norm_num; norm_cast; norm_num
            _ = 2*((2:ℝ)^x)^3:= by ring_nf
            _ = _ := by ring_nf
        have _2: (2:ℝ)^(x*2) = (2^x)^2 := by
          rw [rpow_mul]; norm_cast; norm_num
        have _3: (2:ℝ)^(3+x) = 8 * 2^x := by
          rw [rpow_add]; norm_num; linarith;
        rw [_1, _2, _3]; ring_nf
      _ = _ := by rw [h]

  -- Take variable change y=2^x
  let y:ℝ:= 2^x
  have hyp: y > 0 := by positivity
  have hy1: y*(2* y^2 - 17*y + 8) = 0 := by
    unfold y
    exact h1

  -- Factorization
  have hy: 2*y*(y-8)*(y- 1/2) = 0 := by
    calc
      _ = y*(2* y^2 - 17*y + 8) := by ring_nf
      _ = _ := by exact hy1
  simp at hy

  -- Case 1: when $2^x = 0$, it has no solution.
  have c1: y = 0 → False := by
    intro a
    have d: y ≠ 0 := by positivity
    contradiction

  rcases hy with ha | hc

  -- 2. $2^x-8 = 0$. Then, we have $x=\log_2 8$ = 3
  have : y - 8 = 0 := by tauto
  have : y = 8 := by linarith
  have : x = 3 := by
    calc
      _ = logb 2 y := by
        unfold y; rw [logb_rpow]; norm_num; norm_num
      _ = _ := by
        rw [this, show 8 = (2:ℝ)^3 by norm_num, logb_pow]; norm_num
  tauto
  -- Case 3: when $2^x = 1/2$, x = -1
  have : x = -1 := by
    calc
      _ = logb 2 y := by
        unfold y; rw [logb_rpow]; norm_num; norm_num
      _ = _ := by
        rw [show y = 1/2 by linarith, show 1/2 = (2:ℝ)^(-1:ℝ) by norm_num, logb_rpow]; norm_num; norm_num
  tauto


              

