import Mathlib

namespace Algebra_609100
def point (k : ℝ)  (n : ℤ) : ℤ × ℝ := (n, n * k) 

def sq_dis (k : ℝ)  (m : ℤ) (n : ℤ) : ℝ := ((m : ℤ) - n) ^ 2 + ((@point k n).2 - (@point k m).2) ^ 2
end Algebra_609100

open Algebra_609100

theorem Algebra_609100 {k : ℝ} (h : ∀ (n : ℤ), sq_dis k (n) (n + 4) = 31 ^ 2) :
  ∀ (n : ℤ), sq_dis k n (n + 12) = 93 ^ 2 :=  by
  have dis_eq : ∀ (n : ℤ), ∀ (d : ℤ), sq_dis k n (n + d) = sq_dis k 0 d := by 
    intro n d
    unfold sq_dis
    unfold point
    simp
    ring
  intro n
  rw [dis_eq n 12]
  unfold sq_dis
  unfold point
  simp
  obtain h := h n
  unfold sq_dis at h
  unfold point at h
  simp at h
  ring_nf at h
  rw [mul_pow]
  have k_sq : k ^ 2 = (945) / (16 : ℝ) := by 
    calc
      _ = (k ^ 2 * 16) / (16 : ℝ) := by 
        field_simp
      _ = (961 - 16) / (16 : ℝ) := by 
        rw [←h]
        simp
      _ = (945) / (16 : ℝ) := by 
        norm_num
  rw [k_sq]
  norm_num
  
