import Mathlib

/-
Given a positive integer \( n \geq 2 \), determine the largest positive integer \( N \) for which there exist \( N+1 \) real numbers \( a_{0}, a_{1}, \ldots, a_{N} \) such that:
(1) \( a_{0}+a_{1}=-\frac{1}{n} \), and
(2) \(\left(a_{k}+a_{k-1}\right)\left(a_{k}+a_{k+1}\right)=a_{k-1}-a_{k+1}\) for \( 1 \leq k \leq N-1 \).

Proposed by: Romania
-/

/-
Define a function `satisfy_list` that generates the sequence of real numbers satisfying the given conditions.
The function recursively calculates values based on the conditions provided.
-/
noncomputable def satisfy_list (n i:ℕ) : ℝ :=
  match i with
  | 0 => 0
  | Nat.succ j => -(1/(n-j)) - satisfy_list n j

theorem algebra_605817 (n : ℕ) (hn : 2 ≤ n) :
    IsGreatest {N | 0 < N ∧ ∃ a : ℕ → ℝ, a 0 + a 1 = -(1 / n) ∧ ∀ k ∈ Finset.Icc 1 (N - 1), (a k + a (k - 1)) * (a k + a (k + 1)) = a (k - 1) - a (k + 1)} n := by
      constructor
      /-
      First, prove that \( n \) satisfies the conditions.
      -/
      · simp
        constructor
        /-
        Show that \( n > 0 \).
        -/
        · linarith
        /-
        Construct the sequence `a` using `satisfy_list`.
        -/
        · let a:= (satisfy_list n)
          use a
          /-
          Establish the relationship between consecutive elements.
          -/
          have heq : ∀ k, a k + a (k+1) = - (1/(n-k)) := by
            intro k
            have : a (k+1) = -(1/(n-k)) - a k := by
              unfold a
              rw [satisfy_list]
            rw [this]
            field_simp
          constructor
          /-
          Verify the initial condition \( a_0 + a_1 = -\frac{1}{n} \).
          -/
          · have := heq 0
            simp at this
            exact this
          /-
          Verify the main condition for all \( k \).
          -/
          · intro k hk1 hk2
            have heq1 : a k + a (k-1) = -(1/(n-(k-1))) := by
              have := heq (k-1)
              have hone : k - 1 + 1 = k := by exact Nat.sub_add_cancel hk1
              rw [hone] at this
              rw [add_comm, this]
              norm_cast
            have heq2 : a k + a (k+1) = -(1/(n-k)) := by
              rw [heq k]
            symm
            calc
              _ = a (k-1) + a k - (a k + a (k+1)) := by ring_nf
              _ = -(1/(n-(k-1))) - (-(1/(n-k))) := by rw [add_comm, heq1, heq2]
              _ = -(1/(n-(k-1)) - 1/(n-k)) := by
                apply Eq.symm (neg_sub' ((1:ℝ)/(n-(k-1))) ((1:ℝ)/(n-k)))
              _ = (1/((n-(k-1)) * (n-k))) := by
                have : (1:ℝ)/(n-(k-1)) - 1/(n-k) = -1/((n-(k-1)) * (n-k)) := by
                  have h1: (1:ℝ)/(n-(k-1)) = (n-k)/((n-(k-1)) * (n-k)) := by
                    have : (n:ℝ) - k ≠ 0 := by
                      intro h
                      have : (n:ℝ) = k := by
                        calc
                          _ = (n:ℝ) - k + k := by ring
                          _ = _ := by rw [h]; ring
                      norm_num at this
                      rw [this] at hk2
                      have : k + 1 ≤ k := by
                        calc
                          _ ≤ k - 1 + 1 := by linarith
                          _ = _ := Nat.sub_add_cancel hk1
                      linarith
                    rw [@div_mul_cancel_right₀ ℝ _ ((n:ℝ)-k) this ((n:ℝ)-(k-1))]
                    simp
                  have h2: (1:ℝ)/(n-k) = (n-(k-1))/((n-(k-1)) * (n-k)) := by
                    have : (n:ℝ) - (k-1) ≠ 0 := by
                      intro h
                      have : (n:ℝ) + 1 = k := by
                        calc
                          _ = 1 + ((n:ℝ) - (k-1)) + (k-1) := by ring
                          _ = _ := by rw [h]; ring
                      norm_cast at this
                      rw [← this] at hk2
                      have : n + 2 ≤ n := by
                        calc
                          _ = n + 1 + 1 := by ring
                          _ ≤ n - 1 + 1 := by linarith
                          _ = _ := Nat.sub_add_cancel (by linarith)
                      linarith
                    rw [@div_mul_cancel_left₀ ℝ _ ((n:ℝ)-(k-1)) this ((n:ℝ)-k)]
                    simp
                  rw [h1, h2, div_sub_div_same]
                  have : (n:ℝ) - k - (n - (k - 1)) = -1 := by
                    ring_nf
                  rw [this]
                rw [this]
                field_simp
              _ = _ := by
                rw [heq1, heq2]
                field_simp
      /-
      Next, prove that no larger \( N \) can satisfy the conditions.
      -/
      · intro N hN
        simp at hN
        /-
        Assume for contradiction that there exists an \( N > n \) satisfying the conditions.
        -/
        by_contra hge
        simp at hge
        rcases hN with ⟨hpos, ⟨a, ⟨ha1, ha2⟩⟩⟩
        /-
        Define a helper sequence \( b \) where \( b(i) = a(i) + a(i+1) \).
        This sequence simplifies the manipulation of the conditions.
        -/
        let b (i:ℕ) : ℝ := a i + a (i+1)
        /-
        Establish a key property of the sequence \( b \) for \( 1 \leq k \leq N-1 \).
        Specifically, show that \((b(k-1) + 1) \times (b(k) - 1) = -1\).
        -/
        have hb : ∀ k, 1 ≤ k → k ≤ N - 1 → (b (k-1) + 1) * (b k -1) = -1 := by
          intro k hk1 hk2
          calc
            _ = b (k-1) * b k - (b (k-1) - b k) - 1 := by ring_nf
            _ = (a k + a (k - 1)) * (a k + a (k + 1)) - (a (k - 1) - a (k + 1)) - 1 := by
              unfold b
              field_simp
              ring
            _ = _ := by
              rw [ha2 k hk1 hk2]
              ring
        /-
        Prove that for \( 0 \leq k < n \), \( b(k) = -\frac{1}{n-k} \).
        This establishes a specific form for \( b \) that leads to a contradiction.
        -/
        have hbeq : ∀ k, 0 ≤ k → k < n → b k = -1/(n-k) := by
          intro k
          induction k with
          | zero =>
            intro _ _
            unfold b
            simp
            rw [ha1]
            ring
          | succ k hk =>
            intro hk1 hk2
            have : n ≤ N - 1 := by exact (Nat.le_sub_one_iff_lt hpos).mpr hge
            have heq := hb (k+1) (by linarith) (by linarith)
            field_simp at heq
            rw [hk (by linarith) (by linarith)] at heq
            /-
            Simplify and manipulate the equation to find the form of \( b(k+1) \).
            -/
            have : -(1:ℝ) / (n - k) + 1 = (n - (k+1))/(n-k) := by
              calc
                _ = -(1:ℝ) / (n - k) + (n-k) / (n-k) := by
                  simp
                  symm
                  apply div_self
                  intro hzero
                  have : (n:ℝ) = k := by
                    rw [← sub_zero (n:ℝ), ← hzero]
                    simp
                  norm_cast at this
                  rw [this] at hk2
                  linarith
                _ = _ := by ring
            rw [this] at heq
            /-
            Show that \( (b(k+1) - 1) = -\frac{1}{(n-(k+1))/(n-k)} \).
            This is crucial for establishing the contradiction.
            -/
            have : (b (k + 1) - 1) = -1 / ((n - (k + 1)) / (n - k)) := by
              nth_rw 1 [← heq]
              symm
              apply mul_div_cancel_left₀
              simp
              constructor
              · intro hzero
                have : (n:ℝ) = k + 1 := by
                  rw [← sub_zero (n:ℝ), ← hzero]
                  simp
                norm_cast at this
                rw [this] at hk2
                linarith
              · intro hzero
                have : (n:ℝ) = k := by
                  rw [← sub_zero (n:ℝ), ← hzero]
                  simp
                norm_cast at this
                rw [this] at hk2
                linarith
            rw [div_div_eq_mul_div (-(1:ℝ)) (n - (k + 1)) (↑n - ↑k)] at this
            simp at this
            calc
              _ = b (k + 1) - 1 + 1 := by ring
              _ = (k - n) / (n - (k + 1)) + 1 := by rw [this]
              _ = (k - n) / (n - (k + 1)) + (n - (k + 1)) / (n - (k + 1)) := by
                simp
                symm
                apply div_self
                intro hzero
                have : (n:ℝ) = k + 1 := by
                  rw [← sub_zero (n:ℝ), ← hzero]
                  simp
                norm_cast at this
                rw [this] at hk2
                linarith
              _ = _ := by
                rw [div_add_div_same]
                simp
        /-
        Arrive at a contradiction by applying the established properties to the sequence.
        Specifically, show that the derived form of \( b(n-1) \) contradicts the properties of \( b \).
        -/
        have := hbeq (n-1) (Nat.le_sub_one_of_lt (by linarith)) (Nat.sub_one_lt_of_lt hn)
        field_simp at this
        have hzero := hb n (by linarith) ((Nat.le_sub_one_iff_lt hpos).mpr hge)
        rw [this] at hzero
        field_simp at hzero
