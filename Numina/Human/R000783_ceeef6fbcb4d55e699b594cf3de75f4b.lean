import Mathlib

/- Let $f$ be a function taking the positive integers to the positive integers, such that

(i) $f$ is increasing (i.e. $f(n + 1) > f(n)$ for all positive integers $n$)
(ii) $f(mn) = f(m) f(n)$ for all positive integers $m$ and $n,$ and
(iii) if $m \neq n$ and $m^n = n^m,$ then $f(m) = n$ or $f(n) = m.$

Find the sum of all possible values of $f(30).$ -/
theorem algebra_15282 (f : ℕ → ℕ) (h₀ : ∀ n, 0 < n → 0 < f n) (h₁ : ∀ m n, 0 < m → 0 < n → f m * f n = f (m * n)) (h₂ : ∀ n, 0 < n → f (n + 1) > f n) (h₃ : ∀ m n, 0 < m → 0 < n → m ≠ n → m ^ n = n ^ m → f m = n ∨ f n = m) :
    f 30 = 900 := by
  -- Substitute 2 and 4 into h₃.
  specialize h₃ 2 4
  simp at h₃
  -- Show that f(4) ≠ 2.
  have h₄ : f 4 > 2 := by
    calc
      f 4 ≥ f 3 + 1 := by apply h₂; norm_num
      _ ≥ f 2 + 1 + 1 := by apply Nat.add_le_add_right; apply h₂; norm_num
      _ ≥ 1 + 1 + 1 := by rw [add_assoc, add_assoc]; apply Nat.add_le_add_right; apply h₀; norm_num
  replace h₄ : f 4 ≠ 2 := by
    linarith only [h₄]
  simp [h₄] at h₃
  -- Show that f(2 ^ n) = 4 ^ n for all n > 0.
  replace h₄ (n : ℕ) : f (2 ^ (n + 1)) = 4 ^ (n + 1) := by
    induction n with
    | zero =>
      norm_num
      exact h₃
    | succ n hn =>
      rw [Nat.pow_add]
      rw [<-h₁]
      simp [h₃]
      nth_rewrite 2 [Nat.pow_add]
      repeat simp [hn]
  -- Show that f(3) ≥ 9.
  have h₅ : f 3 ^ 2 > 64 := by
    calc
      f 3 ^ 2 = f 9 := by rw [Nat.pow_two, h₁]; repeat norm_num
      _ > f 8 := by apply h₂; norm_num
      _ = 64 := by rw [show 8 = 2 ^ (2 + 1) by norm_num, h₄]; norm_num
  replace h₅ : f 3 > 8 := by
    by_contra! h₅
    rw [show 8 = Nat.sqrt 64 by norm_num, Nat.le_sqrt'] at h₅
    omega
  -- Show that f m < f n if m < n.
  have h₂' (m n : ℕ) : 0 < m → 0 < n → m < n → f m < f n := by
    intro mpos _ mltn
    apply Nat.exists_eq_add_of_lt at mltn
    obtain ⟨k, hmn⟩ := mltn
    rw [hmn]
    clear hmn
    induction k with
    | zero =>
      apply h₂
      exact mpos
    | succ k hk =>
      calc
        f m < f (m + k + 1) := by exact hk
        _ < f (m + (k + 1) + 1) := by rw [<-add_assoc]; apply h₂; simp
  -- Show that f(3) ≤ 9, hence f(3) = 9.
  have h₆ : f 3 ^ 8 < 10 ^ 8 := by
    calc
      f 3 ^ 8 = f 3 ^ (1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) := by norm_num
      _ = f (3 ^ (1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) := by rw [Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add]; simp; rw [h₁, h₁, h₁, h₁, h₁, h₁, h₁]; all_goals norm_num
      _ = f (3 ^ 8) := by norm_num
      _ < f (2 ^ 13) := by apply h₂'; all_goals norm_num
      _ = 4 ^ 13 := by rw [h₄]
      _ < 10 ^ 8 := by norm_num
  replace h₆ : f 3 < 10 := by
    contrapose! h₆
    rw [show 10 ^ 8 = (10 ^ 4) ^ 2 by norm_num, show f 3 ^ 8 = (f 3 ^ 4) ^ 2 by rw [<-Nat.pow_mul], Nat.le_sqrt'.symm, Nat.sqrt_eq']
    rw [show 10 ^ 4 = (10 ^ 2) ^ 2 by norm_num, show f 3 ^ 4 = (f 3 ^ 2) ^ 2 by rw [<-Nat.pow_mul], Nat.le_sqrt'.symm, Nat.sqrt_eq']
    rw [Nat.le_sqrt'.symm, Nat.sqrt_eq']
    exact h₆
  replace h₆ : f 3 = 9 := by
    omega
  clear h₅
  -- Show that f(3 ^ n) = 9 ^ n for all n > 0.
  replace h₇ (n : ℕ) : f (3 ^ (n + 1)) = 9 ^ (n + 1) := by
    induction n with
    | zero =>
      norm_num
      exact h₆
    | succ n hn =>
      rw [Nat.pow_add]
      rw [<-h₁]
      simp [h₆]
      nth_rewrite 2 [Nat.pow_add]
      repeat simp [hn]
  -- Show that f(5) ≤ 25.
  have h₈ : f 5 ^ 3 < 26 ^ 3 := by
    calc
      f 5 ^ 3 = f 5 ^ (1 + 1 + 1) := by norm_num
      _ = f (5 ^ (1 + 1 + 1)) := by rw [Nat.pow_add, Nat.pow_add]; simp; rw [h₁, h₁]; all_goals norm_num
      _ = f (5 ^ 3) := by norm_num
      _ < f (2 ^ 7) := by apply h₂'; all_goals norm_num
      _ = 4 ^ 7 := by rw [h₄]
      _ < 26 ^ 3 := by norm_num
  replace h₈ : f 5 < 26 := by
    contrapose! h₈
    apply Nat.pow_le_pow_left
    exact h₈
  -- Show that f(5) ≥ 25, hence f(5) = 25.
  have h₉ : f 5 ^ 11 > 24 ^ 11 := by
    calc
      f 5 ^ 11 = f 5 ^ (1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) := by norm_num
      _ = f (5 ^ (1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) := by rw [Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add]; simp; rw [h₁, h₁, h₁, h₁, h₁, h₁, h₁, h₁, h₁, h₁]; all_goals norm_num
      _ = f (5 ^ 11) := by norm_num
      _ > f (3 ^ 16) := by apply h₂'; all_goals norm_num
      _ = 9 ^ 16 := by rw [h₇]
      _ > 24 ^ 11 := by norm_num
  replace h₉ : f 5 > 24 := by
    contrapose! h₉
    apply Nat.pow_le_pow_left
    exact h₉
  replace h₉ : f 5 = 25 := by
    omega
  clear h₈
  -- Show f(30) = 900.
  calc
    f 30 = f (2 * 3 * 5) := by norm_num
    _ = f 2 * f 3 * f 5 := by rw [h₁, h₁]; all_goals norm_num
    _ = 900 := by rw [h₃, h₆, h₉]
