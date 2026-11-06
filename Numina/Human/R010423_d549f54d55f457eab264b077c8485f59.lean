import Mathlib

open Polynomial Finset

/-Emile a créé un exercice pour Benoît. Il lui annonce qu'il a choisi secrètement un polynôme P unitaire de degré 2023 à coefficients entiers, c'est-à-dire de la forme

$$
P(X)=X^{2023}+a_{2022} X^{2022}+a_{2021} X^{2021}+\ldots+a_{1} X+a_{0}
$$

où $a_{0}, a_{1}, \ldots, a_{2022}$ sont des entiers relatifs. Il donne à Benoît $k$ entiers $n_{1}, n_{2}, \ldots, n_{k}$, où $k$ est un entier positif, ainsi que la valeur du produit $P\left(n_{1}\right) P\left(n_{2}\right) \ldots P\left(n_{k}\right)$. A partir de ces connaissances, Benoît doit essayer de retrouver le polynôme P .
Trouver l'entier $k$ minimal tel que Emile puisse trouver $P$ et $n_{1}, \ldots, n_{k}$ afin de s'assurer que le seul polynôme coincidant avec les informations données à Benoît soit P .-/
theorem algebra_607170 : IsLeast {k | ∃ n : ℕ → ℤ, ∃ P : Polynomial ℤ, P.Monic ∧ P.natDegree = 2023 ∧
∀ Q : Polynomial ℤ, Q.Monic ∧ Q.natDegree = 2023 ∧ ∏ i ∈ range k, Q.eval (n i) = ∏ i ∈ range k, P.eval (n i) → P = Q} 2023 := by
-- Generalize $2023$ to any positive odd integer $l$
  have lpos : 0 < 2023 := by simp
  have lodd : Odd 2023 := by use 1011; simp
  generalize 2023 = l at lpos lodd
  rw [IsLeast, lowerBounds]; simp; constructor
  -- According to the reference answer, define a function $n$ to be $3*i$ for any $i$
  -- and define a polynomial $P$ to be the product of $x-3i$'s for $i=0,1,2...l-1$ plus $1$
  · let n : ℕ → ℤ := fun i => 3 * i; let P : Polynomial ℤ := ∏ i ∈ range l, (X - C (n i)) + C 1
  -- Prove that $n$ is injective
    have ninj : n.Injective := by simp [n]; intro; intros; simp_all
  -- Prove that $P$ is monic
    have Pmoni : P.Monic := by
      simp only [P]; apply Monic.add_of_left; apply monic_prod_of_monic
      intros; apply monic_X_sub_C
      rw [degree_C, ← natDegree_pos_iff_degree_pos]
      rw [natDegree_prod]; apply sum_pos; intros; rw [natDegree_X_sub_C]; simp
      use 0; simp; exact lpos; intros; apply X_sub_C_ne_zero; simp
  -- Prove that the degree of $P$ is $l$
    have degP : P.natDegree = l := by
      simp only [P]; rw [natDegree_add_eq_left_of_degree_lt, natDegree_prod]
      nth_rw 2 [show l = ∑ i ∈ range l, 1 by simp]; apply sum_congr rfl
      intros; apply natDegree_X_sub_C; intros; apply X_sub_C_ne_zero
      rw [degree_C, ← natDegree_pos_iff_degree_pos, natDegree_prod]; apply sum_pos
      intros; rw [natDegree_X_sub_C]; simp
      use 0; simp; exact lpos; intros; apply X_sub_C_ne_zero; simp
  -- Prove that $P(n_i)=1$ for any $i < l$
    have Peval : ∀ i ∈ range l, P.eval (n i) = 1 := by
      intro i hi; simp [P, eval_prod]; apply prod_eq_zero hi; simp
    use n; use P; split_ands; any_goals assumption
  -- Take any monic polynomial of degree $l$ satisfying the property in question
    intro Q Qmoni degQ hPQ; simp [prod_congr rfl Peval] at hPQ
  -- Prove that the absolute value of $Q(n_i)$ is $1$ for any $i < l$
    have absQeval : ∀ i ∈ range l, |eval (n i) Q| = 1 := by
      intro i hi; suffices : |eval (n i) Q| ∣ 1
      · apply Int.eq_one_of_dvd_one; simp; exact this
      rw [← hPQ]; apply dvd_trans (show |eval (n i) Q| ∣ eval (n i) Q by rw [abs_dvd])
      apply dvd_prod_of_mem; exact hi
  -- Prove that $Q(n_i)$ is congruent $Q.coeff 0$ modulo $3$ for any $i < l$
    have Qevalmod3 : ∀ i ∈ range l, eval (n i) Q % 3 = Q.coeff 0 % 3 := by
      intro i hi; simp [n]; have : Q.natDegree < l + 1 := by simp [degQ]
      rw [eval_eq_sum_range' this, add_comm, sum_range_add]; simp
      simp_rw [add_comm, mul_comm, pow_succ']
      have : ∑ x ∈ range l, (i:ℤ) * 3 * (i * 3) ^ x * Q.coeff (x + 1) =
      3 * ∑ x ∈ range l, i * (i * 3) ^ x * Q.coeff (x + 1) := by
        rw [mul_sum]; apply sum_congr rfl; intros; ring
      rw [this, Int.add_mul_emod_self_left]
  -- Prove that $Q(n_i)$ is equal to $P(n_i)$ for any $i < l$
    have Qeval : ∀ i ∈ range l, Q.eval (n i) = P.eval (n i) := by
      intro i hi; rw [Peval i hi]
      rcases ((abs_eq (show (0:ℤ)≤1 by simp)).mp (absQeval i hi)) with _|hr; assumption
      suffices : ∀ j ∈ range l, Q.eval (n j) = -1
      · simp [prod_congr rfl this] at hPQ; rw [Odd.neg_one_pow lodd] at hPQ; contradiction
      intro j hj; rcases ((abs_eq (show (0:ℤ)≤1 by simp)).mp (absQeval j hj)) with hl|_
      · apply_fun fun t => t % 3 at hr hl; rw [Qevalmod3] at hr hl
        norm_num at hr hl; linarith; all_goals assumption
      assumption
  -- Apply eq_of_degree_le_of_eval_finset_eq on the image set $n(range l)$ to finish the goal
    apply eq_of_degree_le_of_eval_finset_eq (image n (range l))
    · rw [card_image_iff.mpr]; apply degree_le_of_natDegree_le; simp [degP]; apply ninj.injOn
    · rw [degree_eq_natDegree, degree_eq_natDegree, degP, degQ]; all_goals intro h; simp_all
    · rw [Monic.leadingCoeff, Monic.leadingCoeff]; all_goals assumption
    simp; intro i hi; symm; apply Qeval; simp; exact hi
-- For any natural number $k$ less than $l$, any monic polynomial $P$ of degree $l$ and any sequence of numbers $n_i$
-- we construct a monic polynomial $Q$ of the same degree satisfying the desired properties in question with $P≠Q$
  intro k n P Pmoni degP h; by_contra! klt; let Q := P + ∏ i ∈ range k, (X - C (n i))
-- Prove an auxillary degree inequality
  have deglt : (∏ i ∈ range k, (X - C (n i))).natDegree < P.natDegree := by
    rw [natDegree_prod]
    have : ∀ i ∈ range k, (X - C (n i)).natDegree = 1 := by intros; apply natDegree_X_sub_C
    rw [sum_congr rfl this, degP]; simp; exact klt
    intros; apply X_sub_C_ne_zero
-- Prove $P≠Q$
  have PneQ : P ≠ Q := by
    intro h'; simp [Q] at h'; rw [prod_eq_zero_iff] at h'; rcases h' with ⟨j, ⟨⟩⟩
    have : X - C (n j) ≠ 0 := by apply X_sub_C_ne_zero
    contradiction
-- Prove that $Q$ satisfies all the desired property
  suffices : P = Q; contradiction; apply h
  · apply Monic.add_of_left; exact Pmoni; apply degree_lt_degree; exact deglt
  · rw [natDegree_add_eq_left_of_degree_lt]; exact degP
    apply degree_lt_degree; exact deglt
  apply prod_congr rfl; intro i hi; simp [Q, eval_prod]; apply prod_eq_zero hi; simp