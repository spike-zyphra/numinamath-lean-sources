import Mathlib

/- We define the relation `Reachable n m` to mean that Gandalf can reach world `m` from world `n`. -/
inductive Reachable : ℕ → ℕ → Prop
-- First six relations are the ones given in the problem.
| Rab : ∀ n ≥ 1, Reachable n (2 * n)
| Rac : ∀ n ≥ 1, Reachable n (3 * n + 1)
| Rba : ∀ n ≥ 1, Reachable (2 * n) n
| Rbc : ∀ n ≥ 1, Reachable (2 * n) (3 * n + 1)
| Rca : ∀ n ≥ 1, Reachable (3 * n + 1) n
| Rcb : ∀ n ≥ 1, Reachable (3 * n + 1) (2 * n)
| refl : ∀ n ≥ 1, Reachable n n -- Gandalf can stay in the same world.
| trans : ∀ {m n k}, Reachable m n → Reachable n k → Reachable m k -- Gandalf can reach world `k` from world `m` if he can reach world `n` from world `m` and world `k` from world `n`.

/- We show that `Reachable` is symmetric. -/
def Reachable.symm {n m : ℕ} (h : Reachable n m) : Reachable m n := by
  -- By induction on the relation `h`, we can show that `Reachable` is symmetric.
  induction h with
  -- First six relations are the ones given in the problem.
  -- They are all symmetric.
  | Rab n hn => exact Reachable.Rba n hn
  | Rac n hn => exact Reachable.Rca n hn
  | Rba n hn => exact Reachable.Rab n hn
  | Rbc n hn => exact Reachable.Rcb n hn
  | Rca n hn => exact Reachable.Rac n hn
  | Rcb n hn => exact Reachable.Rbc n hn
  -- `refl` and `trans` are symmetric themselves.
  | refl n hn => exact Reachable.refl n hn
  | trans hmn hnk ih₁ ih₂ => exact ih₂.trans ih₁

/- We show that from any world `n` with `1 < n`, we can reach a world `m` with `1 ≤ m < n`. -/
def lemma_1 {n : ℕ} (hn : 1 < n) : ∃ m < n, 1 ≤ m ∧ Reachable n m := by
  -- We consider the three cases of `n` modulo 3.
  mod_cases h : n % 3
  all_goals
    -- We write `n` as `3 * k + r` for `r` in {0, 1, 2}.
    obtain ⟨k, hk⟩ : ∃ k, n = 3 * k + n % 3 := ⟨n / 3, (Nat.div_add_mod n 3).symm⟩
    rw [h] at hk
    simp at hk
    clear h
    -- Substituting `n` with `3 * k + r`
    subst n
  . -- Case `n = 3 * k`.
    -- `3 * k + 1` → `3 * (3 * k) + 1` → `2 * (3 * (3 * k) + 1)` → `2 * (2 * (3 * (3 * k) + 1))`
    have h₁ : Reachable (3 * k) (3 * (3 * k) + 1) := Reachable.Rac _ (by omega)
    have h₂ : Reachable (3 * (3 * k) + 1) (2 * (3 * (3 * k) + 1)) := .Rab _ (by omega)
    have h₃ : Reachable (2 * (3 * (3 * k) + 1)) (2 * (2 * (3 * (3 * k) + 1))) := .Rab _ (by omega)
    have h₄ := h₁.trans (h₂.trans h₃)
    -- `2 * (2 * (3 * (3 * k) + 1))` = `3 * (3 * (2 * (2 * k)) + 1) + 1`.
    convert_to Reachable (3 * k) (3 * (3 * (2 * (2 * k)) + 1) + 1) at h₄
    . ring
    -- `3 * (3 * (2 * (2 * k)) + 1) + 1` → `3 * (2 * (2 * k)) + 1` → `2 * (2 * k)` → `2 * k`.
    have h₅ : Reachable (3 * (3 * (2 * (2 * k)) + 1) + 1) ((3 * (2 * (2 * k)) + 1)) := .Rca _ (by omega)
    have h₆ : Reachable ((3 * (2 * (2 * k)) + 1)) (2 * (2 * k)) := .Rca _ (by omega)
    have h₇ : Reachable (2 * (2 * k)) (2 * k) := .Rba _ (by omega)
    -- `2 * k` is OK.
    exact ⟨2 * k, by omega, by omega, h₄.trans (h₅.trans (h₆.trans h₇))⟩
  . -- Case `n = 3 * k + 1`.
    -- `3 * k + 1` → `k`.
    -- `k` is OK.
    exact ⟨k, by omega, by omega, .Rca k (by omega)⟩
  . -- Case `n = 3 * k + 2`.
    -- `3 * k + 2` → `3 * (3 * k + 2)`
    have h₁ : Reachable (3 * k + 2) (2 * (3 * k + 2)) := .Rab _ (by omega)
    -- `3 * (3 * k + 2)` = `3 * (2 * k + 1) + 1`.
    convert_to Reachable (3 * k + 2) (3 * (2 * k + 1) + 1) at h₁
    . ring
    -- `3 * (2 * k + 1) + 1` → `2 * k + 1`.
    have h₂ : Reachable (3 * (2 * k + 1) + 1) (2 * k + 1) := .Rca _ (by omega)
    -- `2 * k + 1` is OK.
    exact ⟨2 * k + 1, by omega, by omega, h₁.trans h₂⟩

/- We show that from any world `n` with `1 ≤ n`, we can reach world `1`. -/
def lemma_2 {n : ℕ} (hn : 1 ≤ n) : Reachable n 1 := by
  -- Use second principle of induction.
  induction n using Nat.strongRec with
  | ind n ih =>
    -- If `n = 1`, then `Reachable 1 1` is trivial.
    rcases hn.eq_or_lt with rfl | hn
    . exact Reachable.refl _ hn
    -- Otherwise, we can reach a world `m` with `1 ≤ m < n` from `n` by the first lemma.
    rcases lemma_1 hn with ⟨m, hm, h₁, h₂⟩
    -- So we can reach `1` from `m` from `n` by transitivity and the induction hypothesis.
    exact h₂.trans (ih m hm h₁)

/- The worlds in the Worlds' Sphere are numbered $1,2,3, \ldots$ and connected so that for any integer $n \geqslant 1$, Gandalf the Wizard can move in both directions between any worlds with numbers $n, 2 n$ and $3 n+1$. Starting his travel from an arbitrary world, can Gandalf reach every other world? -/
theorem number_theory_238858 (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) : Reachable n m := by
  -- We can reach `1` from `n` and `m` by the second lemma.
  have h₁ : Reachable n 1 := lemma_2 hn
  have h₂ : Reachable m 1 := lemma_2 hm
  -- By symmetry, we can reach `m` from `1`.
  -- By transitivity, we can reach `m` from `1` from `n`.
  exact h₁.trans h₂.symm