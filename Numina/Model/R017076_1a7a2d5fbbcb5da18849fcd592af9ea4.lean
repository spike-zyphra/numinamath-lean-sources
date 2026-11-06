import Mathlib

open Finset Real

theorem algebra_134121 {p : ℕ → ℝ} (hp0 : p 0 = 1) (hp1 : p 1 = 0)
    (hpn : ∀ n, p (n + 1) = (1 - p n) * (1 / 3)) :
    p 2020 = (1 / 3) * (1 - (-1 / 3)^2019) / (1 - (-1 / 3)) := by

  have eq2 : ∀ (n : ℕ), p n = (3 / 4) * (-1 / 3) ^ n + (1 / 4) := by
    intro n 
    induction n with
    | zero =>
      rw [hp0]
      norm_num
    | succ n ih =>
      have eq3 := hpn n
      rw [eq3]
      rw [ih]
      field_simp
      ring_nf
  have h2020 : p 2020 = (3 / 4) * (-1 / 3) ^ 2020 + (1 / 4) := eq2 2020
  rw [h2020]
  field_simp
  ring_nf