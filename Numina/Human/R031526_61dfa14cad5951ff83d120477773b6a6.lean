import Mathlib

theorem algebra_324310 {a : ℕ → ℝ} {c : ℝ} (hc : c > 0)
    (ha : ∀ n, 0 < a n) (h : ∀ n, a (n + 1) = a n + c * (a n)^2) :
    ∀ M, 0 < M → ∃ N, ∀ n, N < n → a n > M := by
  intro M hM
  have ha_mono : StrictMono a := by
    refine strictMono_nat_of_lt_succ fun n ↦ ?_
    simp [h, hc]
    exact sq_pos_of_pos (ha n)
  have hda_mono : Monotone (fun n ↦ c * a n ^ 2) := by
    intro n₁ n₂ hn
    have h₁ := ha_mono.monotone hn
    simp [hc]
    exact (sq_le_sq₀ (le_of_lt (ha _)) (le_of_lt (ha _))).mpr h₁
  replace hda_mono : Monotone (fun n ↦ a (n + 1) - a n) := by
    convert hda_mono using 1
    ext n
    linear_combination h n
  have H (n : ℕ) : a n ≥ n * (a 1 - a 0) + a 0 := by
    induction n with
    | zero => simp
    | succ n ih =>
      calc a (n + 1)
        _ = a n + (a (n + 1) - a n) := by ring
        _ ≥ n * (a 1 - a 0) + a 0 + (a 1 - a 0) := add_le_add ih (hda_mono (show 0 ≤ n by simp))
        _ = (n + 1) * (a 1 - a 0) + a 0 := by ring
        _ = ↑(n + 1) * (a 1 - a 0) + a 0 := by simp
  have ⟨N, hN⟩ := Archimedean.arch M (show 0 < a 1 - a 0 from sub_pos.mpr (ha_mono (show 0 < 1 by simp)))
  simp at hN
  use N
  intro n hn
  calc a n
    _ > a N := ha_mono hn
    _ ≥ N * (a 1 - a 0) + a 0 := H N
    _ > N * (a 1 - a 0) := lt_add_of_pos_right _ (ha 0)
    _ ≥ M := hN
