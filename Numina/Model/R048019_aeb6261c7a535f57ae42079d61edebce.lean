import Mathlib

theorem algebra_323053 {f : ℤ → ℤ} (hf : ∃ p : Polynomial ℤ, ∀ x : ℤ, f x = p.eval x)
    (h1 : f (-2) = -56) (h2 : f 1 = -2) (h3 : f 3 = 53) (h4 : f 6 = 528) :
    f 3 ≠ 53 := by
  rcases hf with ⟨p, hp⟩
  have eq1 : f (-2) = p.eval (-2) := hp (-2)
  rw [eq1] at h1
  have eq2 : f 1 = p.eval 1 := hp 1
  rw [eq2] at h2
  have eq3 : f 3 = p.eval 3 := hp 3
  rw [eq3] at h3
  have eq4 : f 6 = p.eval 6 := hp 6
  rw [eq4] at h4
  by_contra h
  have h5 : p.eval 3 = 53 := by linarith
  -- For integer polynomials, the difference $p(a) - p(b)$ is divisible by $a-b$.
  -- Let's consider $p(6) - p(3)$, which should be divisible by $6-3=3$.
  have h6 : (p.eval 6 - p.eval 3) % 3 = 0 := by
    have h7 : (6 - 3 : ℤ) ∣ (p.eval 6 - p.eval 3) := by
      apply p.sub_dvd_eval_sub
    obtain ⟨k, hk⟩ := h7
    omega
  -- Now we substitute the given values
  have h7 : p.eval 6 = 528 := by linarith
  have h8 : p.eval 3 = 53 := by linarith [h5]
  -- Now $p(6) - p(3) = 528 - 53 = 475$
  have h9 : (p.eval 6 - p.eval 3) % 3 = 1 := by
    rw [h7, h8]
    all_goals norm_num
  -- This contradicts the requirement from the polynomial divisibility
  omega