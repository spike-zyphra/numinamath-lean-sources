import Mathlib

/- Let $n>1$ be an integer. Find, with proof, all sequences $x_{1}, x_{2}, \ldots, x_{n-1}$ of positive integers with the following three properties: (a) $x_{1}<x_{2}<\cdots<x_{n-1}$; (b) $x_{i}+x_{n-i}=2 n$ for all $i=1,2, \ldots, n-1$; (c) given any two indices $i$ and $j$ (not necessarily distinct) for which $x_{i}+x_{j}<2 n$, there is an index $k$ such that $x_{i}+x_{j}=x_{k}$. -/
open Finset
theorem number_theory_604213 (n : ℕ) (hn : 1 < n) (x: ℕ → ℕ):
    ((∀i∈Ico 1 n, x i > 0) ∧ 
      (StrictMonoOn x (Ico 1 n)) ∧
      (∀i ∈ Ico 1 n, 
          x i + x (n - i) = 2 * n) ∧
      (∀i ∈ Ico 1 n,
        ∀j ∈ Ico 1 n,
          x i + x j < 2 * n → 
            ∃k ∈ Ico 1 n, x i + x j = x k)) ↔ ∀k ∈ Ico 1 n, x k = 2 * k := by
  apply Iff.intro
  -- The -> direction
  · rintro ⟨h_pos, h_mono, h_symm, h_sum⟩ k hk
    -- we need an auxiliary lemma showing that (n - 1) ∈ Ico 1 n
    have h_n_sub_1_in_ico: (n - 1) ∈ Ico 1 n := by
      simp; omega
    -- another lemma reasoning about membership of Ico 1 (n - 1) and Ico 1 n
    have h_j_sub_aux: ∀{j}, j ∈ Ico 1 (n - 1) → j ∈ Ico 1 n := by
      simp; omega
    -- first due to monotonicity, we have x j < x (n - 1) where j < n - 1
    have h_le: ∀j∈Ico 1 (n-1), x j < x (n-1) := by
      intro j hj
      -- next we transform j < n-1 to eliminate subtraction
      simp at hj;
      have hj' := Nat.add_lt_of_lt_sub' hj.2
      -- applying the monotonicity where j < n - 1
      (apply h_mono (a := j) (b := n - 1)) <;> try simp; try omega
      exact hj.2
    -- first, the sequence x 1 + x j < x 1 + x (n - 1) = 2 * n where j < n - 1 due to monotonicity
    have h_one_add: ∀j∈Ico 1 (n - 1), x 1 + x j < 2 * n := by
      intro j hj
      apply lt_of_lt_of_eq (b := x 1 + x (n - 1))
      · simp; apply h_le _ hj
      · apply h_symm 1 (by simp; linarith)
    -- next, we show that x 1 + x j and x (j + 1) coincide.
    have h_eq: ∀j∈Ico 1 (n-1), x 1 + x j = x (j + 1) := by
      -- first we can interpret the equation as two functions
      let f₁: {j: ℕ // j ∈ Ico 1 (n - 1)} → ℕ := λj => x 1 + x j.val
      let f₂: {j: ℕ // j ∈ Ico 1 (n - 1)} → ℕ := λj => x (j.val + 1)
      -- apparently, f₁ is strictly monotone
      have h₁: StrictMono f₁ := by
        rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
        unfold f₁
        simp
        apply h_mono (h_j_sub_aux ha) (h_j_sub_aux  hb) hab
      -- similarly for f₂
      have h₂: StrictMono f₂ := by
        rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
        unfold f₂
        simp
        -- to show the monotonicity, we first show a + 1/b + 1 being in the range, then a+1<b+1
        apply h_mono
        · simp; simp at ha; apply Nat.add_lt_of_lt_sub ha.2
        · simp; simp at hb; apply Nat.add_lt_of_lt_sub hb.2
        · simp at hab
          linarith
      -- it suffices to show that these two functions are the same
      suffices hf: f₁ = f₂
      · -- first we can write out the equation based on f₁ and f₂
        intro j hj
        generalize hj': (Subtype.mk j hj) = j'
        have h₁: x 1 + x j = f₁ j' := by unfold f₁; rw [<-hj']
        have h₂: x (j + 1) = f₂ j' := by unfold f₂; rw [<-hj']
        -- next, we represent the result with f₁ and f₂
        rw [h₁, h₂, hf]
      · -- next, the equality of the function follows from their monotonicity and they having the same range
        rw [<-StrictMono.range_inj h₁ h₂]

        · -- we show same range by showing f₁'s range is a subset of f₂'s, and then same cardinality
          apply Set.eq_of_subset_of_card_le
          intro fx hfx
          obtain ⟨⟨j, hj⟩, hfx_j⟩ := hfx
          -- use property c, and also knowing that x 1 + x j < 2 * n
          have hc := h_sum 1 (by simp; assumption) j (h_j_sub_aux hj) (h_one_add j hj)
          -- extarct k from property c
          obtain ⟨k', hk'_sub, hk'_eq⟩ := hc
          -- apparently k' > 1 due to x being monotone
          have hk': k' > 1 := by
            simp
            rw [<-StrictMonoOn.lt_iff_lt (a := 1) h_mono _ hk'_sub]
            -- we are left with x 1 < x k' = x 1 + x j
            · simp [<-hk'_eq]
              -- and we know that elements are positive integers
              apply h_pos
              apply (h_j_sub_aux hj)
            · -- finally showing 1 is in the domain of the function
              simp; assumption
          -- we know that k' - 1 must be in the domain of f₂
          have hk'': k' - 1 ∈ Ico 1 (n - 1) := by
            simp
            constructor
            · apply Nat.le_sub_of_add_le'; linarith
            · simp at hk'_sub
              omega
          -- we now show that fx is in the range of f₂, by showing it is the value at f₂ j + 1
          generalize h_k'': Subtype.mk (k'-1) hk'' = k''
          use k''
          unfold f₂
          -- next we leverage the explicity form of k', showing that it is the same as f₁ j
          simp [<-h_k'']
          rw [Nat.sub_add_cancel (by linarith)]
          rw [<-hfx_j, <-hk'_eq]
          unfold f₁
          -- next we need to show the two range are the same as the domain size from them being monotone (hence injective)
          have h₁_inj_on := h₁.injective.encard_image Set.univ
          have h₂_inj_on := h₂.injective.encard_image Set.univ
          simp at h₁_inj_on h₂_inj_on
          -- next we normalize the types of card to natural numbers
          rw [Set.encard_eq_coe_toFinset_card, Set.encard_eq_coe_toFinset_card] at h₁_inj_on h₂_inj_on
          rw [Set.toFinset_card, Set.toFinset_card] at h₁_inj_on h₂_inj_on
          -- eliminate the ENat conversion on w.r.t the cardinality
          norm_cast at h₁_inj_on h₂_inj_on
          rw [h₁_inj_on, h₂_inj_on]
    -- we next show x k = k * x 1 by induction leveraging h_eq
    have h_xk_eq_k_m {k}: k ∈ Ico 1 n → x k = k * x 1 := by
      intro hk
      induction k
      · simp at hk
      · -- the induction start with k being 1
        rename_i k' hk'
        cases k'
        · -- k' = 0, hence k' + 1 = 1
          simp
        · rename_i k'
          simp at hk hk'
          -- we first show that k' + 1 < n and k' + 1 < n - 1
          have h': k' + 1 < n := by linarith
          have h'': k' + 1 < n - 1 := by apply Nat.lt_sub_of_add_lt hk
          -- first we know that x (k' + 1) = (k' + 1) * x 1
          specialize hk' h'
          -- then we leverage h_eq to get the value of x (k' + 1 + 1)
          specialize h_eq (k' + 1) (by simp; omega)
          -- eliminating all x using h_eq and hk' we can complete the proof
          linarith [h_eq, hk']
    -- finally x 1 is 2 through property b
    have h_x_1: x 1 = 2 := by
      -- first applying h_xk_eq_k_m, since (n - 1) is in Ico 1 n, therefore, x (n - 1) = (n - 1) * x 1
      specialize h_xk_eq_k_m (k := n - 1) (by simp; refine ⟨Nat.le_sub_of_add_le (by linarith), by linarith⟩)
      -- and we can get x 1 + x (n - 1) = n * x 1
      have h': x 1 + x (n - 1) = n * x 1 := by
        -- rearranging the term we get x (n - 1) + x 1 = n * x 1
        rw [add_comm]
        symm
        -- we want to move x 1 to the left: n * x 1 - x 1 = x (n - 1)
        apply Nat.eq_add_of_sub_eq
        · -- we then show x 1 ≤ n * x 1, following the fact that x 1 is an positive integer
          specialize h_pos 1 (by simp; linarith)
          field_simp
          linarith
        · simp [h_xk_eq_k_m, Nat.sub_mul]
      -- then from h_symm x 1 + x (n - 1) = 2 * n
      specialize h_symm 1 (by simp; linarith)
      simp [h'] at h_symm
      nlinarith
    -- finally, leveraging h_xk_eq_k_m, we can show x k = 2 * k
    rw [h_x_1] at h_xk_eq_k_m
    rw [mul_comm]
    apply h_xk_eq_k_m hk
  · -- for the inversed direction, we simply replace x k with 2 * k
    intro hk;
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- x k = 2 * k is positive since k is positive
      intro i hi
      simp [hk i hi]
      simp at hi
      linarith
    · -- x k is monotonic because k itself is
      intro a ha b hb hab
      -- we can simply replace x a = 2 * a and  x b = 2 * b
      rw [hk a ha, hk b hb]
      linarith
    · -- x k satisfies property c since 2 * i + 2 * (n - i) = 2 * n
      intro i hi
      rw [hk i hi, hk (n - i)]
      rw [Nat.mul_sub, <-Nat.add_sub_assoc]
      · simp
      · simp at hi; linarith
      · -- we show n - i is indeed in Ico 1 n
        simp at hi; simp
        -- we need then to show 1 ≤ n - i ∧ 0 < n ∧ 0 < i, and when we convert the first goal into 1 ≤ n - i, we can just use linarith
        (refine ⟨?_, ?_, ?_⟩; apply Nat.le_sub_of_add_le) <;> linarith
    · -- finally we can find an index (i + j)
      intro i hi j hj hij
      -- replacing x i and x j with 2 * i and 2 * j
      rw [hk i hi, hk j hj] at *
      use (i + j)
      -- we show that (i + j) is indeed in Ico 1 n so we can repalce them with 2 *(i+j)
      have h_i_add_j: (i + j) ∈ Ico 1 n := by
        simp_all
        -- we need to show 1 ≤ i + j ∧ i + j < n
        constructor <;> linarith
      simp [<-mul_add] at hij
      -- finally we need to show: i + j ∈ Ico 1 n ∧ 2 * i + 2 * j = x (i + j)
      refine ⟨h_i_add_j, ?_⟩
      · rw [hk (i + j) h_i_add_j, <-mul_add]
