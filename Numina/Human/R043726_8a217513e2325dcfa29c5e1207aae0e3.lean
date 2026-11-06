import Mathlib

def fib (n : ℕ) : ℕ := match n with
| 0 => 1
| 1 => 1
| n + 2 => fib n + fib (n + 1)

/- The Fibonacci sequence is constructed as follows: each term is the sum of the two preceding ones. Its first terms are:

$$
1,1,2,3,5,8,13,21,34,55,89, \ldots
$$

Show that the Fibonacci sequence contains a multiple of 1000.-/
theorem number_theory_292559 : ∃ n, 1000 ∣ fib n := by 
  -- Notons $F_{n}$ le $n$-ième terme de la suite de Fibonacci ( $F_{1}=1, F_{2}=1, F_{3}=2$, etc.) et notons $u_{n}$ le reste de la division euclidienne de $F_{n}$ par 1000 ( $u_{n}$ est donc le nombre formé par les trois derniers chiffres de $F_{n}$ ). 
  let u := fun (n : ℕ) => fib n % 1000
  -- ) d'entiers compris entre 0 et 999 (il y en a exactement $1000^{2}=1000000$ ), il existe des entiers $n$ et $N$ tels que $N&gt;0$ et
  -- $$ u_{n}=u_{n+N} \quad ; \quad u_{n+1}=u_{n+1+N} $$
  let xy := fun (n : ℕ) => 1000 * u n + u (n+1)
  have h1 : ∃ m n : ℕ, m ≠ n ∧ xy n = xy m := by 
    by_contra! hmn
    have : ∀ K,K ≤ ((Finset.range K).image xy).card := by
      intro K
      apply Finset.le_card_of_inj_on_range xy
      simp
      intro i hi ;use i
      intro i hi j hj hij
      specialize hmn i j
      simp [hij] at hmn
      exact hmn
    have this' : ∀ K, (Finset.range K).image xy ⊆ Finset.range (1000*1000) := by 
      intro K x
      simp
      intro i hi hx
      rw [← hx]
      simp [xy]
      have : u i < 1000 ∧ u (i+1) < 1000 := by simp [u] ;constructor <;> apply Nat.mod_lt <;> norm_num
      omega
    have this'' : ∀ K, ((Finset.range K).image xy).card ≤ (Finset.range (1000*1000)).card := by
      intro K
      specialize this' K
      apply Finset.card_le_card at this'
      exact this'
    specialize this 2000000
    specialize this'' 2000000
    simp at this'' ;linarith
  rcases h1 with ⟨m,n,hmn,hmn'⟩
  let t := min m n
  let N := max m n - min m n
  have h2 : xy t = xy (t+N) := by
    simp [t,N]
    by_cases hm:m ≤ n
    · simp [hm,hmn']
    have hn : n ≤ m := by linarith
    simp [hn,hmn']
  have h3 : 0 < N := by
    simp at hmn ;simp [N] ;exact fun a => hmn (id (Eq.symm a))
  have hmod : ∀ t, xy t % 1000 = u (t+1) := by
    intro t ;simp [xy,Nat.add_mod,u]
  have hdiv : ∀ t, xy t / 1000 = u t := by
    intro t ;simp [xy,Nat.add_div,u, Nat.mod_lt]
  have ht : u t = u (t+N) ∧ u (t+1) = u (t+1+N) := by
    constructor
    · rw [← hdiv t,← hdiv (t+N),h2]
    rw [← hmod t,add_comm (t+1),← add_assoc,add_comm N,← hmod (t+N),h2]
  -- Or, $u_{n-1}$ (resp. $\left.u_{n-1+N}\right)$ s'obtient à partir de $u_{n}$ et $u_{n+1}$ (resp. $u_{n+N}$ et $u_{n+1+N}$ ) comme le reste de la division euclidienne de $u_{n+1}-u_{n}$ (resp. $u_{n+1+N}-u_{n+N}$ ) par 1000. 
  have h4 : ∀ n , (u (n+2) ≥ u (n+1) → u n = u (n+2) - u (n+1)) ∧ (u (n+2) <  u (n+1) → u n = u (n+2) + 1000 - u (n+1)) := by
    intro n
    constructor
    intro hn
    simp [u,fib]
    rw [Nat.add_mod]
    by_cases h : fib n % 1000 + fib (n + 1) % 1000 < 1000
    · rw [Nat.mod_eq_of_lt h,Nat.add_sub_cancel]
    simp at h
    have : fib n % 1000 + fib (n + 1) % 1000 - 1000 < 1000 := by omega
    simp [u,fib] at hn
    rw [Nat.add_mod,Nat.mod_eq_sub_mod h,Nat.mod_eq_of_lt this] at hn
    omega
    intro hn
    simp [u,fib]
    by_cases h : 1000 ≤ fib n % 1000 + fib (n + 1) % 1000
    rw [Nat.add_mod,Nat.mod_eq_sub_mod h]
    have : fib n % 1000 + fib (n + 1) % 1000 - 1000 < 1000 := by omega
    rw [Nat.mod_eq_of_lt this,Nat.sub_add_cancel,Nat.add_sub_cancel] ;linarith
    simp at h
    simp [u,fib] at hn
    rw [Nat.add_mod,Nat.mod_eq_of_lt h] at hn ;simp at hn 
  -- Ainsi, des égalités (1), on déduit que $u_{n-1}=u_{n-1+N}$. En continuant ainsi, on obtient $u_{N+1}=u_{1}=1$ et $u_{N+2}=u_{2}=1$,
  have h5 : ∀ n m, u (n+m) = u (m) → u (n+m+1) = u (m+1) → u n = u 0 ∧ u (n+1) = u 1:= by
    intro n m p1 p2
    induction m with
    | zero => 
      simp at p1 p2
      simp [p1,p2]
    | succ m ih =>
      have : u (n + m) = u m := by
        by_cases h : u (n + m + 2) ≥ u (n + m  + 1) 
        · have h6 := h4 (n+m)
          rcases h6 with ⟨h61,h62⟩
          have h7 := h61 h
          have h8 := h4 m 
          rcases h8 with ⟨h81,h82⟩
          ring_nf at p1 p2 h h81
          rw [p1,p2] at h
          have h9 := h81 h
          rw [h7,h9,← p1,← p2] ;ring_nf
        have h6 := h4 (n+m)
        rcases h6 with ⟨h61,h62⟩
        simp at h
        have h7 := h62 h
        have h8 := h4 m 
        rcases h8 with ⟨h81,h82⟩
        ring_nf at p1 p2 h h82
        rw [p1,p2] at h
        have h9 := h82 h
        rw [h7,h9,← p1,← p2] ;ring_nf
      apply ih this ;rw [← p1] ;ring_nf
  -- d'où il résulte enfin $u_{N}=0$. L'entier $F_{N}$ est donc multiple de 1000 .
  specialize h5 N t
  rw [ht.1,ht.2] at h5
  ring_nf at h5 ;simp at h5
  specialize h4 (N-1)
  rcases h4 with ⟨h41,h42⟩
  have : N - 1 + 2 = N + 1 := by
    zify ;omega
  have this' : N - 1 + 1 = N := by omega
  rw [this,this',h5.1,add_comm,h5.2] at h41
  simp [u,fib] at h41
  use (N-1) ;exact Nat.dvd_of_mod_eq_zero h41

