import Mathlib

open Real Set
open scoped Real

/- 15. $\log _{\cos x} \sin x-2 \log _{\sin x} \cos x+1=0$. -/
theorem algebra_189236 {x : ℝ} (hcos: 0 < cos x) (hsin: 0 < sin x) (hlogcos: log (cos x) ≠ 0) (hlogsin: log (sin x)≠ 0):
    logb (cos x) (sin x) - 2 * logb (sin x) (cos x) + 1 = 0 ↔ 
    ∃ k : ℤ, (x = π / 4 + π * k) := by
    
    --Some basic facts needed later about bounds on x. These are trivial to prove using known trigonometric identities.
    have pipos: 0 < π := by exact pi_pos
    have cosl1: cos x < 1 := by 
      have : cos x ≤ 1 := by exact cos_le_one x
      by_contra h
      have : cos x = 1 := by linarith
      have : cos x = 1 ∨ cos x = -1 := by tauto
      rw [←Real.sin_eq_zero_iff_cos_eq] at this
      linarith
    have cosgm1: -1 < cos x := by 
      have : -1 ≤ cos x := by exact neg_one_le_cos x
      by_contra h
      have : cos x = -1 := by linarith
      have : cos x = 1 ∨ cos x = -1 := by tauto
      rw [←Real.sin_eq_zero_iff_cos_eq] at this
      linarith
    have sinxl1: sin x < 1 := by 
      have : sin x ≤ 1 := by exact sin_le_one x
      by_contra h
      have : sin x = 1 := by linarith
      simp_all
    have sinxgm1: -1 < sin x := by 
      have : -1 ≤ sin x := by exact neg_one_le_sin x
      by_contra h
      have : sin x = -1 := by linarith
      simp_all
    
    constructor
    intro h

    --We prove that sin x = cos x, by rewriting our equation.
    have : sin x = cos x := by 
      have: logb (sin x) (cos x) = 1 / logb (cos x) (sin x) := by
        rw [←inv_logb]
        simp
      rw [this] at h
      field_simp at h
      have : logb (cos x) (sin x) ≠ 0 := by 
        refine logb_ne_zero_of_pos_of_ne_one_of_base_lt_one hcos cosl1 hsin ?_
        linarith
      field_simp [this] at h
      have : logb (cos x) (sin x) * logb (cos x) (sin x) - 2 + logb (cos x) (sin x) = (logb (cos x) (sin x) +2) * (logb (cos x) (sin x)-1 ):= by ring
      rw [this] at h
      have : (logb (cos x) (sin x) + 2) =0 ∨ (logb (cos x) (sin x) - 1) =0 := by exact mul_eq_zero.mp h

      --So sin x = (cos x)^(-2) or sin x = cos x. The first one cannot happen.
      rcases this with m2 | p1
    
      have : logb (cos x) (sin x) = -2 := by linarith
      rw [Real.logb_eq_iff_rpow_eq] at this
      have : 1 < cos x ^ (-(2:ℝ)) := by 
        refine one_lt_rpow_of_pos_of_lt_one_of_neg hcos cosl1 ?_
        linarith
      have : 1 < sin x := by linarith
      exfalso; linarith
      linarith
      linarith
      linarith

      have : logb (cos x) (sin x)  = 1 := by linarith
      rw [Real.logb_eq_iff_rpow_eq] at this
      rw [← this]
      exact rpow_one (cos x)
      repeat linarith

    --So we get tan x = 1, and hence x has to be π /4 + nπ .
    have tanxe1: tan x = 1 := by 
      rw [tan_eq_sin_div_cos]; field_simp; 
      exact this
    let k:ℤ := ⌊x/π⌋
    use k
    have : x = π / 4 + k * π := by 
      let y := x - k * π 
      have hxy : x = y + k*π := by simp [y]
      have uby1: y < π := by 
        simp [y,k]
        refine Int.sub_floor_div_mul_lt x ?_
        exact pipos
      have lby: 0 ≤ y := by 
        simp [y,k]
        have sl: ⌊x/π⌋ ≤ x/π := by exact Int.floor_le (x / π)
        exact (le_div_iff₀ pipos).mp sl
      have : tan y = tan x := by
        simp [y]
        apply Real.tan_sub_int_mul_pi x k
      have tany: tan y = 1 := by rw[tanxe1] at this; exact this
      have : y < π /2 := by 
        by_contra ygepio2; push_neg at ygepio2
        by_cases yepio2 : y = π /2
        rw [yepio2] at tany; norm_num at tany
        have ygpio2 : π / 2 < y := by exact lt_of_le_of_ne ygepio2 fun a => yepio2 (id (Eq.symm a))
        have : tan y < 0 := by 
          have : tan y = tan (y - π) := by exact Eq.symm (tan_sub_pi y)
          rw [this]
          refine tan_neg_of_neg_of_pi_div_two_lt ?_ ?_
          linarith
          linarith
        linarith
      have tanpio4: tan (π / 4)= 1 := by simp
      have : tan y = tan (π /4) := by linarith
      apply Real.tan_inj_of_lt_of_lt_pi_div_two at this
      rw [this] at hxy
      exact hxy
      linarith
      linarith
      linarith
      linarith
    
    rw [mul_comm]
    exact this

    --For another direction. Simple calculation to verify that  x = π /4 + nπ satisfies the original equation.
    intro h
    obtain ⟨k,hk⟩ := h
    have : sin x = cos x := by 
      have : tan x = 1 := by 
        rw [hk]
        have : tan (π / 4) = tan (π /4 + π * k) := by 
          rw [mul_comm]
          symm
          exact Real.tan_add_int_mul_pi (π/4) k
        rw [← this]
        simp
      rw [tan_eq_sin_div_cos] at this
      field_simp at this
      exact this
    rw [this]
    simp [logb, hlogcos]
    norm_num