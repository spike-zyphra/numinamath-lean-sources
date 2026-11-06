import Mathlib.Tactic

/-
PROBLEM:
Doug can paint a room in $5$ hours. Dave can paint the same room in $7$ hours. Doug and Dave paint the room together and take a one-hour break for lunch. Let $t$ be the total time, in hours, required for them to complete the job working together, including lunch. Which of the following equations is satisfied by $t$?
$\mathrm{(A)}\ \left(\frac{1}{5}+\frac{1}{7}\right)\left(t+1\right)=1\qquad\mathrm{(B)}\ \left(\frac{1}{5}+\frac{1}{7}\right)t+1=1\qquad\mathrm{(C)}\ \left(\frac{1}{5}+\frac{1}{7}\right)t=1\\\mathrm{(D)}\ \left(\frac{1}{5}+\frac{1}{7}\right)\left(t-1\right)=1\qquad\mathrm{(E)}\ \left(5+7\right)t=1$
-/

theorem alg_1187
  (t w : ℝ)
  (r₁ r₂ r : ℚ)
  (doug_rate : r₁ = 1 / 5)
  (dave_rate : r₂ = 1 / 7)
  (combined_rate : r = r₁ + r₂)
  (total_work_time : w = t - 1) :
  r * w = 1 ↔ t = 47 / 12 := by
    -- tackle one direction at a time
    apply Iff.intro
    · rw [combined_rate, total_work_time, doug_rate, dave_rate]
      intro h
      field_simp at h
      field_simp
      norm_num at h
      rw [mul_sub] at h
      norm_num at h
      linarith
    · intro h
      rw [combined_rate, total_work_time, doug_rate, dave_rate]
      rw [h]
      ring