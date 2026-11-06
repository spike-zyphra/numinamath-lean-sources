import Mathlib

def a : ℕ → ℕ
| 0 => 8
| 1 => 3
| (n + 2) => (a (n + 1) + a n) % 10

def move (x : ℕ × ℕ) : ℕ × ℕ := ⟨x.snd, (x.fst + x.snd) % 10⟩

-- Another version of sequence `a`, which is easier to show periodicity.
def a' : ℕ → ℕ × ℕ
| 0 => (8, 3)
| n + 1 => move (a' n)


theorem number_theory_286497 :
  a 2010 = 2 :=
by
  -- We show two versions are equivalent.
  have lemma_1 : ∀ n, a n = (a' n).fst ∧ a (n + 1) = (a' n).snd  := by
    intro n
    induction n with
    | zero => simp [a, a']
    | succ n ih =>
      simp [a, a', move]
      rw [ih.1, ih.2]
      constructor
      . rfl
      . omega

  -- Periodicity
  have lemma_3 : ∀ k, a' 0 = a' k → ∀ n, a' n = a' (n + k) := by
    intro k h n
    induction n with
    | zero => simp; tauto
    | succ n ih =>
      rw [show n + 1 + k = n + k + 1 by ring_nf]
      simp [a']
      rw [ih]
  -- Another periodicity, easy to use.
  have lemma_4 : ∀ k, a' 0 = a' k → ∀ n m , a' n = a' (n + m * k) := by
    intro k h n m
    induction m with
    | zero => simp
    | succ m ih =>
      ring_nf
      trans a' (n + m * k)
      . assumption
      . apply lemma_3
        assumption
  -- Back to main goal
  have : 2010 = 30 + 33 * 60 := by simp
  have H : a' 2010 = a' 30 := by
    rw [this]
    symm
    apply lemma_4
    simp[a', move]
  apply_fun (Prod.fst) at H
  have : (a' 2010).1 = a 2010 := by
    symm
    exact (lemma_1 2010).1
  rw [this] at H
  have : (a' 30).1 = a 30 := by
    symm
    exact (lemma_1 30).1
  rw [this] at H
  rw [H]
  simp [a]
