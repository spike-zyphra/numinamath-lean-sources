import Mathlib

namespace algebra_24106

/- If a function `f : ℕ → ℕ` maps positive natural numbers to positive natural numbers,
then any iterate `f^[m]` of `f` also maps positive natural numbers to positive natural numbers.
-/
lemma iterate_pos_of_pos {f : ℕ → ℕ} (hf : ∀ n > 0, f n > 0) :
  ∀ m, ∀ n > 0, f^[m] n > 0 := by
  intro m n hn
  induction m with
  | zero => exact hn
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact hf _ ih

/- If a function `f : ℕ → ℕ` is non-decreasing between any positive integer `n`
and its successor `n + 1` (i.e., `f n ≤ f (n + 1)` for all `n > 0`),
then `f` is monotone non-decreasing on the set of positive natural numbers (`Set.Ioi 0`).
-/
lemma monotone_on_Ioi_of_le_succ_of_pos {f : ℕ → ℕ} (hf : ∀ n > 0, f n ≤ f (n + 1)) :
    MonotoneOn f (Set.Ioi 0) := by
  intro a ha b hb hab
  induction hab with
  | refl => rfl
  | step ham hm =>
    simp only [Set.mem_Ioi, Nat.succ_eq_add_one, lt_add_iff_pos_left, add_pos_iff, Nat.lt_one_iff,
      pos_of_gt, or_true] at ha
    rename_i m
    have : m ∈ Set.Ioi 0 := by
      simp only [Set.mem_Ioi, Nat.succ_pos']
      simp only [Nat.le_eq] at ham
      omega
    exact (hm this).trans (hf m this)

end algebra_24106

open algebra_24106

/- Determine all pairs $(f, g)$ of functions from the set of positive integers to itself that satisfy
$$ f^{g(n)+1}(n)+g^{f(n)}(n)=f(n+1)-g(n+1)+1 $$  for every positive integer $n$.
Here, $f^{k}(n)$ means $\underbrace{f(f(\ldots f}_{k}(n) \ldots))$.
Answer. The only pair $(f, g)$ of functions that satisfies the equation is given by
$f(n)=n$ and $g(n)=1$ for all $n$. -/
theorem algebra_24106
    {f g : ℕ → ℕ}
    (hfpos : ∀ n > 0, f n > 0)
    (gpos : ∀ n > 0, g n > 0)
    (hfg : ∀ n > 0, f^[g n + 1] n + g^[f n] n = f (n + 1) - g (n + 1) + 1) :
    ∀ n > 0, f n = n ∧ g n = 1 := by
  have h1 : ∀ n > 0, g^[f n] n > 0 := by
    exact fun n a => iterate_pos_of_pos gpos (f n) n a
  -- Step1 : Note that `f^[g n + 1] n + 1 ≤ f (n + 1)` for all `n > 0`. 
  have h2 : ∀ n > 0, f^[g n + 1] n + 1 ≤ f (n + 1) := by
    intro n hn
    calc
      _ ≤ f^[g n + 1] n + g^[f n] n := by
        apply add_le_add_left
        exact h1 n hn
      _ = f (n + 1) - g (n + 1) + 1 := hfg n hn
      _ ≤ f (n + 1) - 1 + 1 := by
        refine add_le_add_right (tsub_le_tsub_left ?_ (f (n + 1))) 1
        exact gpos (n + 1) (by simp)
      _ = f (n + 1) := by
        have := hfpos (n + 1) (by simp)
        omega
  -- Step2 : Show that `∀ k > 0, ∀ n, n ≥ k → f n ≥ k` 
  have h3 : ∀ k > 0, ∀ n, n ≥ k → f n ≥ k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
      exact hfpos
    | succ k hk ih =>
      -- For `k + 1`, we need to show that `f n ≥ k + 1` for all `n ≥ k + 1`.
      intro n hkn
      -- Since `n ≠ 0`, we can replace `n` with `n + 1`.
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
      have hn : n > 0 := by omega
      -- We can use the induction hypothesis to show that `f^[m] n ≥ k`. 
      have : ∀ m > 0, f^[m] n ≥ k := by
        intro m hm
        induction m, hm using Nat.le_induction with
        | base =>
          simp only [Nat.succ_eq_add_one, zero_add, Function.iterate_one]
          apply ih
          exact Nat.le_of_lt_succ hkn
        | succ m hm ihm =>
          rw [Function.iterate_succ_apply']
          apply ih
          exact ihm
      -- Then `f (n + 1) ≥ f^[g n + 1] n + 1 ≥ k + 1` 
      calc
        _ ≥ f^[g n + 1] n + 1 := h2 n hn
        _ ≥ _ := by
          apply add_le_add_right
          apply this
          omega
  -- Step3 : Show that `f n ≥ n` for all `n > 0` by h3 
  have h4 : ∀ n > 0, f n ≥ n := by
    intro n hn
    exact h3 n hn n (Nat.le_refl n)
  -- Step4 : Show that `f^[m] n ≥ f n` for all `m > 0` and `n > 0` 
  have h5 : ∀ m > 0, ∀ n > 0, f^[m] n ≥ f n := by
    intro m hm n hn
    -- Do induction on `m` to show that `f^[m] n ≥ f n` by h3
    induction m, hm using Nat.le_induction with
    | base => simp
    | succ m hm ihm =>
      calc
        _ ≥ f^[m] n := by
          rw [Function.iterate_succ_apply']
          apply h3
          · exact iterate_pos_of_pos hfpos m n hn
          · rfl
        _ ≥ f n := ihm
  -- Step5 : Show that `f` is monotone non-decreasing on the set of positive natural numbers 
  have h6 : MonotoneOn f (Set.Ioi 0) := by
    -- By lemma, it suffices to show that `f n ≤ f (n + 1)` for all `n > 0`
    apply monotone_on_Ioi_of_le_succ_of_pos
    intro n hn
    -- Note that `f (n + 1) ≥ f^[g n + 1] n + 1 ≥ f n + 1 ≥ f n`
    calc
      _ ≥ _ := h2 n hn
      _ ≥ f n + 1 := by
        apply add_le_add_right
        apply h5
        · omega
        · exact hn
      _ ≥ f n := Nat.le_add_right (f n) 1
  -- Step6 : Show that `f (n + 1) > f (f n)` for all `n > 0`
  have h7 : ∀ n > 0, f (n + 1) > f (f n) := by
    intro n hn
    -- Note that `f^[g n + 1] n ≥ f (f n)` by monotonicity of `f`
    have : f^[g n + 1] n ≥ f (f n) := by
      rw [Function.iterate_succ_apply']
      apply h6
      · exact hfpos n hn
      · apply iterate_pos_of_pos hfpos
        exact hn
      exact h5 (g n) (gpos n hn) n hn
    have eq := h2 n hn
    omega
  -- Step7 : Show that `f n < n + 1` for all `n > 0`
  have h8 : ∀ n > 0, n + 1 > f n := by
    intro n hn
    apply MonotoneOn.reflect_lt h6 (hfpos n hn) (by norm_num)
    exact h7 n hn
  -- Step8 : Show that `f n = n` for all `n > 0`
  have h9 : ∀ n > 0, f n = n := by
    intro n hn
    have ge : f n ≥ n := h4 n hn
    have lt : f n < n + 1 := h8 n hn
    omega
  -- Step9 : Show that `f^[m] n = 1` for all `m` and `n > 0`
  have h10 : ∀ m : ℕ, ∀ n > 0, f^[m] n = n := by
    intro m n hn
    induction m with
    | zero => rfl
    | succ m ih =>
      simp only [Function.iterate_succ, Function.comp_apply]
      rw [h9 n hn, ih]
  -- Step10 : Show that `n + g^[n] n = n + 1 - g (n + 1) + 1` by `f n = n`
  replace hfg : ∀ n > 0, n + g^[n] n = n + 1 - g (n + 1) + 1 := by
    intro n hn
    calc
      _ = f^[g n + 1] n + g^[f n] n := by
        rw [h10 (g n + 1) n hn, h9 n hn]
      _ = f (n + 1) - g (n + 1) + 1 := by
        rw [hfg n hn]
      _ = _ := by
        rw [h9 (n + 1) (by simp)]
  have hgn : ∀ n > 0, g^[n] n > 0 := fun n hn => iterate_pos_of_pos gpos n n hn
  -- Step11 : Show that `g (n + 1) < n + 1` for all `n > 0`, then `n + 1 - g (n + 1) > 0`. 
  have h11 : ∀ n > 0 , g (n + 1) < n + 1 := by
    intro n hn
    by_contra! hg
    have contra := hfg n hn
    have := hgn n hn
    rw [show n + 1 - g (n + 1) = 0 by omega] at contra
    simp only [zero_add] at contra
    absurd contra
    omega
  -- Step12 : Show that `g^[n] n + g (n + 1) = 2` for all `n > 0`
  replace hfg : ∀ n > 0, g^[n] n + g (n + 1) = 2 := by
    intro n hn
    have p1 := h11 n hn
    have p2 := hfg n hn
    omega
  clear* -gpos h9 hgn hfg
  intro n hn
  constructor
  · exact h9 n hn
  · -- Step13 : Show that `g (n + 1) = 1` and `g^[n] n = 1` for all `n > 0`
    have : ∀ n > 0, g (n + 1) = 1 ∧ g^[n] n = 1 := by
      intro n hn
      have h9' := h9 n hn
      have hfg' := hfg n hn
      have hgn' := hgn n hn
      have gpos' := gpos (n + 1) (by simp)
      omega 
    -- Step14 : By induction on `n`, suffices to show that `g n = 1` and `g (n + 1) = 1` for all `n > 0`
    induction n, hn using Nat.le_induction with
    | base => exact (this 1 (by simp)).2
    | succ n hn _ => exact (this n hn).1
