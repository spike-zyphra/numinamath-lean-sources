import Mathlib 

namespace calculus_610984 

theorem Cauchy_Schwarz_Ineq (a b c d : ℝ) :
    (a * c + b * d) ^ 2 ≤ (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by
  have h : 0 ≤ (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) - (a * c + b * d) ^ 2
  calc
    (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) - (a * c + b * d) ^ 2 = (a * d - b * c) ^ 2 := by ring
    _ ≥ 0 := pow_two_nonneg (a * d - b * c)
  calc
    (a * c + b * d) ^ 2  = (a * c + b * d) ^ 2 + 0 := by rw [add_zero]
    _ ≤ (a * c + b * d) ^ 2 + ((a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) - (a * c + b * d) ^ 2) :=
    (add_le_add_iff_left _).2 h
    _ = (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by ring

end calculus_610984 
open Real calculus_610984 

/-What is the minimum vertical distance between the graphs of $2+\sin (x)$ and $\cos (x)$ ?-/
theorem calculus_610984 : IsLeast {a | ∃ x : ℝ, |2 + sin x - cos x| = a} (2 - √2) := by 
  have (a : ℝ) : |2 + sin a - cos a| = 2 + sin a - cos a := by 
  -- Easy to see $2 + \sin x - \cos x \ge 0 \iff |2 + \sin x - \cos x| = 2 + \sin x - \cos x$ 
      rw [abs_eq_self] 
      rw [← ge_iff_le] 
      calc 
        _ ≥ 2 + sin a - 1 := by gcongr ; exact cos_le_one a
        _ ≥ 2 + (- 1) - 1 := by gcongr ; exact neg_one_le_sin a
        _ = 0 := by norm_num 
  conv => enter [1, 1, a, 1, x, 1] ; rw [this]
  constructor 
  · simp only [Set.mem_setOf_eq]
    use - (π / 4)
    rw [sin_neg, cos_neg]
    simp only [sin_pi_div_four, cos_pi_div_four]
    ring 
  --  Take $x=-\pi/4$. Then$|2+\sin x-\cos x| = 2 + \sin x - \cos x = 2 - \sqrt 2.$ 
  · -- Next, we prove $2+\sin x-\cos x \le 2 - \sqrt 2.$
    intro x hx 
    obtain ⟨a, rfl⟩ := hx  
    rw [show 2 + sin a - cos a = 2 - (- sin a + cos a) by ring]
    refine tsub_le_tsub_left ?_ 2 
    -- It suffices to show $\sin x - \cos x \le \sqrt2$
    apply le_sqrt_of_sq_le 
    -- Moreover, $(\sin x - \cos x)^2 \le 2$
    calc 
      _ = ((- 1) * cos a + 1 * sin a) ^ 2 := by ring
      _ ≤ ((- 1) ^ 2 + 1 ^ 2) * ((cos a) ^ 2 + (sin a) ^ 2):= by apply Cauchy_Schwarz_Ineq 
      -- It follows from Cauchy-Schwarts Inequality.
      _ = 2 := by norm_num 
    

