import Mathlib

/- ## Problem B2

Show that we can link any two integers $m, n$ greater than 2 by a chain of positive integers $m=a_{1}, a_{2}, \ldots$, $\mathrm{a}_{\mathrm{k}+1}=\mathrm{n}$, so that the product of any two consecutive members of the chain is divisible by their sum. [For example, $7,42,21,28,70,30,6,3$ links 7 and 3.$]$

 -/
theorem number_theory_211514 (m n : ℕ) (hm : 2 < m) (hn : 2 < n) :
    ∃ k : ℕ, ∃ a : ℕ → ℕ,
      a 0 = m ∧
      a k = n ∧
      (∀ i ∈ Finset.range (k + 1), 0 < a i) ∧
      ∀ i ∈ Finset.range k, (a i + a (i + 1)) ∣ a i * a (i + 1) := by

  -- We write $\mathrm{a} \leftrightarrow \mathrm{b}$ if $(\mathrm{a}+\mathrm{b})$ divides $\mathrm{ab}$.
  -- We will show that $\mathrm{a} \leftrightarrow \mathrm{b}$ is an equivalence relation on the positive integers.
  let r (m n : ℕ) : Prop := ∃ k : ℕ, ∃ a : ℕ → ℕ,
      a 0 = m ∧
      a k = n ∧
      (∀ i ∈ Finset.range (k + 1), 0 < a i) ∧
      ∀ i ∈ Finset.range k, (a i + a (i + 1)) ∣ a i * a (i + 1)
  change r m n

  have hr_trans {a b c : ℕ} (h₁ : r a b) (h₂ : r b c) : r a c := by
    obtain ⟨k₁, f₁, hf₁₀, hf₁k, hpos₁, hdvd₁⟩ := h₁
    obtain ⟨k₂, f₂, hf₂₀, hf₂k, hpos₂, hdvd₂⟩ := h₂
    use k₁ + k₂
    let f (i : ℕ) :=
      if i ≤ k₁ then f₁ i
      else f₂ (i - k₁)
    use f
    split_ands
    · simp [f, hf₁₀]
    · simp [f, hf₂k]
      intro h
      simp [h] at hf₂k ⊢
      rw [←hf₂k, hf₂₀, hf₁k]
    · intro i hi
      simp [f]
      by_cases hi₁ : i ≤ k₁
      · simp [hi₁]
        apply hpos₁
        simp
        exact Order.lt_add_one_iff.mpr hi₁
      · simp [hi₁]
        apply hpos₂
        simp at hi ⊢
        apply Nat.sub_lt_left_of_lt_add
        · push_neg at hi₁
          apply le_of_lt hi₁
        · apply lt_of_lt_of_eq hi
          ring
    · intro i hi
      simp [f]
      by_cases hi₁ : i ≤ k₁
      · simp [hi₁]
        by_cases hi₂ : i + 1 ≤ k₁
        · simp [hi₂]
          apply hdvd₁
          simp
          exact hi₂
        · simp [hi₂]
          push_neg at hi₂
          have : i = k₁ := by
            apply Nat.le_antisymm hi₁
            apply Nat.le_of_lt_succ hi₂
          simp [this, hf₁k, ←hf₂₀]
          simp at hi
          apply hdvd₂
          simp
          have : k₁ < k₁ + k₂ := by
            apply lt_of_le_of_lt ?_ hi
            exact Nat.le_of_lt_succ hi₂
          simp at this
          exact this
      · simp [hi₁]
        simp at hi₁
        have : ¬ i + 1 ≤ k₁ := by simp; apply lt_trans hi₁; simp
        simp [this]
        rw [show i + 1 - k₁ = i - k₁ + 1 by rw [Nat.sub_add_comm (le_of_lt hi₁)]]
        apply hdvd₂
        simp at hi ⊢
        apply Nat.sub_lt_left_of_lt_add
        · apply le_of_lt hi₁
        · exact hi
  have hr_refl (a : ℕ) (ha : a > 0) : r a a := by
    use 0, fun _ => a
    simp
    exact ha
  have hr_symm {a b : ℕ} (h : r a b) : r b a := by
    obtain ⟨k, f, hf₀, hfk, hpos, hdvd⟩ := h
    use k
    let f' (i : ℕ) := f (k - i)
    use f'
    split_ands
    · simp [f', hfk]
    · simp [f', hf₀]
    · intro i hi
      simp [f']
      apply hpos
      simp at hi ⊢
      exact Nat.sub_lt_succ k i
    · intro i hi
      simp [f']
      rw [add_comm, mul_comm]
      have : k - i = k - (i + 1) + 1 := by
        rw [←Nat.sub_sub, Nat.sub_add_cancel]
        simp at hi
        exact Nat.le_sub_of_add_le' hi
      rw [this]
      apply hdvd
      simp at hi ⊢
      exact Nat.zero_lt_of_lt hi
  -- The starting point is that for $\mathrm{n}&gt;1$ we have $\mathrm{n} \leftrightarrow \mathrm{n}(\mathrm{n}-1)$.
  -- As slight variants we also have $2 n \leftrightarrow n(n-2)$ for $n&gt;2$, and in any case where $a \leftrightarrow b$, then also $m a \leftrightarrow m b$ (for $m&gt;0$ ).
  -- That allows us to link $n&gt;2$ and $2 n$, thus: $n \leftrightarrow n(n-1) \leftrightarrow n(n-1)(n-2)=n(n-2) \leftrightarrow 2 n$.
  have hr_double {n : ℕ} (hn : n > 2) : r (2 * n) n := by
    use 4
    let f (i : ℕ) :=
      match i with
      | 0 => 2 * n
      | 1 => n * (n - 2)
      | 2 => n * (n - 1) * (n - 2)
      | 3 => n * (n - 1)
      | 4 => n
      | _ => 0
    use f
    simp
    have h₁ : n > 0 := by linarith only [hn]
    have h₂ : n > 1 := by linarith only [hn]
    constructor
    · intro i hi
      interval_cases i <;> simp [f, hn, h₁, h₂, hn]
    · intro i hi
      interval_cases i <;> simp [f]
      · use 2 * (n - 2)
        apply Int.natCast_inj.mp
        simp
        rw [Nat.cast_sub h₂]
        ring
      · use (n - 1) * (n - 2)
        apply Int.natCast_inj.mp
        simp
        rw [Nat.cast_sub h₁, Nat.cast_sub h₂]
        ring
      · use n * (n - 2)
        apply Int.natCast_inj.mp
        simp
        rw [Nat.cast_sub h₁, Nat.cast_sub h₂]
        ring
      · use n - 1
        apply Int.natCast_inj.mp
        simp
        rw [Nat.cast_sub h₁]
        ring
  -- To go much further we need some inspiration. Note that $n(n-3)+2=(n-1)(n-2)$. So $2(n-1)(n-2) \leftrightarrow n(n$ $-3)(n-1)(n-2)$.
  -- That is critical, for it is a general way of allowing us to reduce the largest factor.
  -- Thus for $n$ $&gt;3, n \leftrightarrow n(n-1) \leftrightarrow n(n-1)(n-2) \leftrightarrow n(n-1)(n-2)(n-3) \leftrightarrow 2(n-1)(n-2) \leftrightarrow(n-1)(n-2) \leftrightarrow n-1$.
  have hr_sub_one {n : ℕ} (hn : n > 3) : r n (n - 1) := by
    apply hr_trans (b := 2 * (n - 1) * (n - 2))
    · use 4
      let f (i : ℕ) :=
        match i with
        | 0 => n
        | 1 => n * (n - 1)
        | 2 => n * (n - 1) * (n - 2)
        | 3 => n * (n - 1) * (n - 2) * (n - 3)
        | 4 => 2 * (n - 1) * (n - 2)
        | _ => 0
      use f
      simp
      have h₁ : n > 0 := by linarith only [hn]
      have h₂ : n > 1 := by linarith only [hn]
      have h₃ : n > 2 := by linarith only [hn]
      constructor
      · intro i hi
        interval_cases i <;> simp [f, hn, h₁, h₂, h₃]
      · intro i hi
        interval_cases i <;> simp [f]
        · use n - 1
          apply Int.natCast_inj.mp
          simp
          rw [Nat.cast_sub h₁]
          ring
        · use n * (n - 2)
          apply Int.natCast_inj.mp
          simp
          rw [Nat.cast_sub h₁, Nat.cast_sub h₂]
          ring
        · use n * (n - 1) * (n - 3)
          apply Int.natCast_inj.mp
          simp
          rw [Nat.cast_sub h₁, Nat.cast_sub h₂, Nat.cast_sub h₃]
          ring
        · use 2 * n * (n - 3)
          apply Int.natCast_inj.mp
          simp
          rw [Nat.cast_sub h₁, Nat.cast_sub h₂, Nat.cast_sub h₃]
          ring
    apply hr_trans (b := (n - 1) * (n - 2))
    · have : r (2 * ((n - 1) * (n - 2))) ((n - 1) * (n - 2)) := by
        apply hr_double
        rw [show 2 = 2 * 1 by rfl]
        apply mul_lt_mul
        · apply Nat.lt_sub_iff_add_lt.mpr
          exact hn
        · apply Nat.lt_sub_iff_add_lt.mpr
          apply lt_trans ?_ hn
          simp
        · simp
        · simp
      rw [mul_assoc]
      exact this
    · use 1, fun x => if x = 0 then (n - 1) * (n - 2) else n - 1
      simp
      split_ands
      · intro i hi
        have h₁ : n > 1 := by linarith only [hn]
        have h₂ : n > 2 := by linarith only [hn]
        interval_cases i <;> (simp [h₁, h₂])
      · use n - 2
        apply Int.natCast_inj.mp
        simp
        rw [Nat.cast_sub, Nat.cast_sub]
        · simp
          ring
        all_goals linarith only [hn]

  -- But linking $n$ and $n-1$ obviously allows us to link any two integers $&gt;3$.
  have hrmn {m n : ℕ} (hn : n > 3) (hm : m > 3) : r m n := by
    wlog hmn : m ≥ n generalizing m n with H
    · push_neg at hmn
      obtain H := H hm hn (le_of_lt hmn)
      exact hr_symm H
    · induction m, hmn using Nat.le_induction
      · apply hr_refl
        linarith only [hn]
      · rename_i m hmn ih
        apply hr_sub_one at hm
        apply hr_trans hm
        rw [Nat.add_sub_cancel]
        have hm : m > 3 := by exact Nat.lt_of_lt_of_le hn hmn
        exact ih hm
  -- That leaves 3 itself, but the question already shows how to link that to at least one integer $&gt;3$, which is all we need.
  have hr3_6 : r 6 3 := by
    use 1, fun x => if x = 0 then 6 else 3
    simp
    constructor
    · intro i hi
      interval_cases i <;> (simp [hn])
    · use 2

  by_cases hn : n ≤ 3
  · have : n = 3 := by
      apply le_antisymm hn
      assumption
    rw [this]
    by_cases hm : m ≤ 3
    · have : m = 3 := by
        apply le_antisymm hm
        assumption
      rw [this]
      apply hr_refl
      simp
    · have hrm_6 : r m 6 := by
        apply hrmn
        simp
        simp at hm
        exact hm
      apply hr_trans hrm_6 hr3_6
  · simp at hn
    by_cases hm : m ≤ 3
    · have : m = 3 := by
        apply le_antisymm hm
        assumption
      rw [this]
      apply hr_symm
      apply hr_trans ?_ hr3_6
      apply hrmn
      · simp
      · exact hn
    · simp at hm
      apply hrmn hn hm
