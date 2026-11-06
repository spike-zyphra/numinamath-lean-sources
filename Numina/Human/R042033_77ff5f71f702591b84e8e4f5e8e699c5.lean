import Mathlib

theorem number_theory_58170 : ∃ n, 1996 ∣ n ∧ (Nat.digits 10 n).sum = 1996 := by
  let f : List ℕ → List ℕ := fun l => [8, 8, 9, 5] ++ l
  have hf : ∀ l, f l = [8, 8, 9, 5] ++ l := by simp [f]
  have nenil : ∀ n, ∀ l, l ≠ [] → f^[n] l ≠ [] := by
    intro n l lne; by_cases h : n ≤ 0
    · simp at h; simp [h]; exact lne
    rw [show n = n-1+1 by omega, Function.iterate_succ_apply', hf]
    apply List.append_ne_nil_of_left_ne_nil; simp
  have aux1 : ∀ n, 1996 ∣ Nat.ofDigits 10 (f^[n] [8, 8, 9, 5]) := by
    intro n; induction n with
    | zero => simp [Nat.ofDigits_eq_sum_mapIdx]; use 3
    | succ n ihn =>
      rw [Function.iterate_succ_apply', hf, Nat.ofDigits_append]
      apply dvd_add
      · simp [Nat.ofDigits_eq_sum_mapIdx]
        use 3; norm_num
      apply dvd_trans ihn; simp
  have aux2 : ∀ n, (f^[n] [8, 8, 9, 5]).sum = 30 * (n + 1) := by
    intro n; induction n with
    | zero => simp
    | succ n =>
      rw [Function.iterate_succ_apply']; dsimp [f] at *
      omega
  have aux3 : ∀ n, ∀ l ∈ f^[n] [8, 8, 9, 5], l < 10 := by
    intro n; induction n with
    | zero => simp
    | succ n ihn =>
      rw [Function.iterate_succ_apply']; intro l hl
      dsimp [f] at hl ihn; repeat rw [List.mem_cons] at hl
      rcases hl with hl|hl|hl|hl|hl; any_goals omega
      exact ihn l hl
  have aux4 : ∀ n, ∀ h : f^[n] [8, 8, 9, 5] ≠ [], (f^[n] [8, 8, 9, 5]).getLast h ≠ 0 := by
    intro n; induction n with
    | zero => simp
    | succ n ihn =>
      intro h; simp_rw [Function.iterate_succ_apply', hf]
      rw [List.getLast_append_right (by apply nenil; simp)]
      apply ihn
  use Nat.ofDigits 10 ([2, 9, 9, 3] ++ [2, 9, 9, 3] ++ (f^[64] [8, 8, 9, 5]))
  constructor
  · repeat rw [Nat.ofDigits_append]
    specialize aux1 64; apply dvd_add
    · simp [Nat.ofDigits_eq_sum_mapIdx]
      use 20002; norm_num
    apply dvd_trans aux1; simp
  rw [Nat.digits_ofDigits]
  repeat rw [List.sum_append]
  rw [aux2]; simp; simp
  intro l hl; repeat rw [List.mem_append] at hl
  rw [or_assoc] at hl; rcases hl with hl|hl|hl
  · simp at hl; omega
  · simp at hl; omega
  exact aux3 64 l hl
  intro h; repeat rw [List.getLast_append_right (by apply nenil; simp)]
  apply aux4