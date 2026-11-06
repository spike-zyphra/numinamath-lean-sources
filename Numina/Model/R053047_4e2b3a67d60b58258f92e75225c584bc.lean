import Mathlib

def a : ℕ → ℕ
| 0 => 2
| n + 1 => a n + 5

def A : Set ℕ := {x | ∃ n, x = n ^ 2}
def B : Set ℕ := {x | ∃ n, x = a n}

theorem number_theory_113327 :
    4017 ∈ B ∧ ¬2014 ∈ B ∧ A ∩ B = ∅ := by
  constructor
  · -- Show 4017 ∈ B
    use 803
    native_decide
  constructor
  · -- Show ¬2014 ∈ B
    intro h
    rcases h with ⟨n, hn⟩
    have h1 : ∀ n : ℕ, a n = 2 + 5 * n := by
      intro n
      induction n with
      | zero =>
        simp [a]
      | succ n ih =>
        simp [a, ih]
        <;> omega
    rw [h1 n] at hn
    -- We get 2 + 5 * n = 2014
    omega
  · -- Show A ∩ B = ∅
    ext x
    simp [A, B, Set.mem_inter]
    intro n hn
    intro m hm
    have h1 : ∀ m : ℕ, a m = 2 + 5 * m := by
      intro m
      induction m with
      | zero =>
        simp [a]
      | succ m ih =>
        simp [a, ih]
        <;> omega
    rw [h1 m] at hm
    -- Now x = n ^ 2 and x = 2 + 5 * m
    -- Therefore n^2 ≡ 2 (mod 5)
    have h2 : n ^ 2 % 5 = 0 ∨ n ^ 2 % 5 = 1 ∨ n ^ 2 % 5 = 4 := by
      have h : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by
        omega
      rcases h with (h | h | h | h | h) <;> norm_num [Nat.pow_mod, h] at *
    -- x = 2 + 5 * m ≡ 2 (mod 5)
    -- Therefore, n^2 ≡ 2 (mod 5), which is impossible
    have h3 : (2 + 5 * m) % 5 = 2 := by
      omega
    -- Now we derive that n^2 ≡ 2 (mod 5)
    have h4 : n ^ 2 % 5 = 2 := by
      omega
    -- Contradiction with h2 and h4
    omega