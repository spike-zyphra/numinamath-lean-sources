import Mathlib

open Real Nat Set Function

/-- Solve the equation 
$$
2x + 1 + \arctan(x) \cdot \sqrt{x^2 + 1}+ \arctan (x + 1) \cdot \sqrt{x^2 + 2x + 2} = 0
$$ -/
theorem Calculus_4205 {x : ℝ} : 2*x + 1 + (arctan x) * √(x^2 + 1) + (arctan (x+1)) * √(x^2 + 2*x + 2) = 0
                      → x = - (1 / 2) := by
  intro h
  -- let $f(x) = x + \arctan(x) \cdot \sqrt{x^2 + 1}$
  let f := fun x => x + arctan x * √(x^2+1)
  -- Then the initial equation can be rewritten as $f(x) + f(x+1)$
  have : f x + f (x + 1) = 2*x + 1 + (arctan x) * √(x^2 + 1) + (arctan (x+1)) * √(x^2 + 2*x + 2) := by
    dsimp [f]; ring_nf
  rw [← this] at h
  -- Note the function $f(x)$ is odd.
  have hfodd : ∀ x, f x = -(f (-x)) := by
    intro x; dsimp [f]
    simp [arctan_neg]; ring_nf
  -- Show the function $f(x)$ is strictly monotonic
  have hfmono : StrictMonoOn f univ := by
    apply StrictMonoOn.add
    · intro _ _ _ _ hab; exact hab
    · intro a _ b _ hab
      simp
      by_cases ha : 0 < a
      · by_cases hb : 0 < b
        · apply mul_lt_mul
          apply Real.arctan_strictMono hab
          apply Real.sqrt_le_sqrt
          nlinarith [hab]
          apply Real.sqrt_pos_of_pos (by nlinarith)
          rw [← Real.arctan_zero]
          apply le_of_lt
          apply Real.arctan_strictMono hb
        · nlinarith
      · by_cases hb : 0 < b
        · by_cases ha' : a = 0
          · rw [ha']
            simp
            apply mul_pos
            rw [← Real.arctan_zero]
            apply Real.arctan_strictMono hb
            exact Real.sqrt_pos_of_pos (by nlinarith)
          have h₁ : arctan a * √(a ^ 2 + 1) < 0 := by
            have : 0 < √(a^2 + 1) := Real.sqrt_pos_of_pos (by nlinarith)
            apply mul_neg_of_neg_of_pos
            rw [← Real.arctan_zero]
            apply Real.arctan_strictMono
            simp at ha
            apply lt_of_le_of_ne ha ha'
            exact this
          have h₂ : 0 < arctan b * √(b ^ 2 + 1) := by
            apply mul_pos
            rw [← Real.arctan_zero]
            apply Real.arctan_strictMono hb
            exact Real.sqrt_pos_of_pos (by nlinarith)
          apply lt_trans h₁ h₂
        · let x := -a
          let y := -b
          have hx : -x = a := by aesop
          have hy : -y = b := by aesop
          have hxpos : 0 < x := by nlinarith
          by_cases h'' : b = 0
          · simp [h'']
            have : 0 < √(a^2 + 1) := Real.sqrt_pos_of_pos (by nlinarith)
            apply mul_neg_of_neg_of_pos
            rw [← Real.arctan_zero]
            apply arctan_strictMono (by nlinarith)
            exact this
          · rw [← hx, ← hy]
            simp
            have hypos : 0 < y := by
              dsimp [y]
              have : b ≤ 0 := by nlinarith
              have : b < 0 := lt_of_le_of_ne this (by aesop)
              linarith
            have hxy : y < x := by linarith
            apply mul_lt_mul
            apply Real.arctan_strictMono hxy
            apply Real.sqrt_le_sqrt
            nlinarith [hxy]
            apply Real.sqrt_pos_of_pos (by nlinarith)
            rw [← Real.arctan_zero]
            apply le_of_lt
            apply Real.arctan_strictMono hxpos
  -- Now we solve the equation $f(x) = -f(x+1)$, i.e. $x = -x + 1$, finally we
  --  get $x = -\frac 1 2$
  rw [← eq_neg_iff_add_eq_zero, hfodd (x + 1)] at h
  simp at h
  rw [StrictMonoOn.eq_iff_eq hfmono (by aesop) (by aesop)] at h
  linarith
