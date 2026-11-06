import Mathlib

namespace Algebra_609100
def point (k : ℝ)  (n : ℤ) : ℤ × ℝ := (n, n * k) 

def sq_dis (k : ℝ)  (m : ℤ) (n : ℤ) : ℝ := ((m : ℤ) - n) ^ 2 + ((@point k n).2 - (@point k m).2) ^ 2
end Algebra_609100

open Algebra_609100

theorem Algebra_609100 {k : ℝ} (h : ∀ (n : ℤ), sq_dis k (n) (n + 4) = 31 ^ 2) :
  ∀ (n : ℤ), sq_dis k n (n + 12) = 93 ^ 2 :=  by
  have eq1 : 16 + 16 * k ^ 2 = 961 := by
    specialize h 0
    norm_num [sq_dis, point] at h ⊢
    linarith
  intro n
  norm_num [sq_dis, point]
  have eq2 : k ^ 2 = (945 / 16 : ℝ) := by
    nlinarith 
  nlinarith [eq2]