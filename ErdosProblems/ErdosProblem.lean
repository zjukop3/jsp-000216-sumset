/-
This is a Lean formalization of a solution to JSP-000216.

The key construction: let A = {n ∈ Nat : every ternary digit of n is 0 or 1}
(the "Cantor set in Nat"). Then A has natural density 0, yet A + A = Nat
(every natural number is a sum of two elements of A). This shows the
sumset of a zero-density set can be as large as possible (all of Nat).

This is a pure Lean 4 proof (no Mathlib dependency).

Formal authors: zjukop3, with OpenAI ChatGPT/Codex assistance.
-/

/-!
# JSP-000216: Sumset of a zero-density set

We construct a set `A ⊆ Nat` with natural density 0 whose sumset `A + A`
equals all of `Nat`. This answers the question "How much larger than a
zero-density integer set can its sumset with itself be?" — the answer is
that the sumset can be all of `Nat` (infinitely larger, density 0 → 1).

The construction is the Cantor set in the natural numbers: the set of
numbers whose base-3 representation uses only digits 0 and 1. This set
has density 0 (there are at most 2^k elements below 3^k), yet every
natural number is a sum of two elements from this set.
-/

namespace Erdos216

/-- The Cantor set in Nat: the smallest set containing 0 and 1, closed
under `n => 3*n` and `n => 3*n+1`. Equivalently, numbers whose ternary
digits are all 0 or 1. -/
inductive Cantor : Nat → Type where
  | zero : Cantor 0
  | one : Cantor 1
  | step0 (n : Nat) (h : Cantor n) : Cantor (3 * n)
  | step1 (n : Nat) (h : Cantor n) : Cantor (3 * n + 1)

/-- List all Cantor-set elements below 3^k. -/
def cantor_list : Nat → List Nat
  | 0 => [0]
  | k + 1 => (cantor_list k).map (fun m => 3 * m) ++ (cantor_list k).map (fun m => 3 * m + 1)

/-- The list has length 2^k. -/
theorem cantor_list_length (k : Nat) : (cantor_list k).length = 2^k := by
  induction k with
  | zero => decide
  | succ k ih =>
    show ((cantor_list k).map (fun m => 3 * m) ++ (cantor_list k).map (fun m => 3 * m + 1)).length = 2 ^ (k + 1)
    rw [List.length_append, List.length_map, List.length_map, ih, Nat.pow_succ]
    omega

theorem zero_mem_list : ∀ k, (0 : Nat) ∈ cantor_list k := by
  intro k
  induction k with
  | zero => decide
  | succ k ih =>
    show 0 ∈ (cantor_list k).map (fun m => 3 * m) ++ (cantor_list k).map (fun m => 3 * m + 1)
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨0, ih, rfl⟩

theorem one_mem_list (k : Nat) (hk : 0 < k) : (1 : Nat) ∈ cantor_list k := by
  cases k with
  | zero => omega
  | succ k' =>
    show 1 ∈ (cantor_list k').map (fun m => 3 * m) ++ (cantor_list k').map (fun m => 3 * m + 1)
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨0, zero_mem_list k', rfl⟩

/-- Every Cantor element below 3^k is in the list. -/
theorem cantor_list_complete (n : Nat) (h : Cantor n) :
    ∀ k : Nat, n < 3^k → n ∈ cantor_list k := by
  induction h with
  | zero =>
    intro k hk
    exact zero_mem_list k
  | one =>
    intro k hk
    exact one_mem_list k (by
      cases k with
      | zero => rw [Nat.pow_zero] at hk; omega
      | succ _ => omega)
  | step0 m hm ih =>
    intro k hk
    show 3 * m ∈ cantor_list k
    cases k with
    | zero =>
      have : m = 0 := by omega
      subst this
      decide
    | succ k' =>
      show 3 * m ∈ (cantor_list k').map (fun m => 3 * m) ++ (cantor_list k').map (fun m => 3 * m + 1)
      rw [Nat.pow_succ] at hk
      have hm_bound : m < 3^k' := by omega
      have hm_mem := ih k' hm_bound
      apply List.mem_append_left
      exact List.mem_map.mpr ⟨m, hm_mem, rfl⟩
  | step1 m hm ih =>
    intro k hk
    show 3 * m + 1 ∈ cantor_list k
    cases k with
    | zero => rw [Nat.pow_zero] at hk; omega
    | succ k' =>
      show 3 * m + 1 ∈ (cantor_list k').map (fun m => 3 * m) ++ (cantor_list k').map (fun m => 3 * m + 1)
      rw [Nat.pow_succ] at hk
      have hm_bound : m < 3^k' := by omega
      have hm_mem := ih k' hm_bound
      apply List.mem_append_right
      exact List.mem_map.mpr ⟨m, hm_mem, rfl⟩

theorem div3_lt (n : Nat) (h : 0 < n) : n / 3 < n := by
  have heq : 3 * (n / 3) + n % 3 = n := Nat.div_add_mod n 3
  have hmod : n % 3 < 3 := Nat.mod_lt n (by decide)
  omega

/-- Recursive helper for the sumset theorem. -/
def cantor_sumset_aux (n : Nat) :
    ∃ (a : Nat) (b : Nat) (ha : Cantor a) (hb : Cantor b), a + b = n := by
  by_cases h0 : n = 0
  · exact ⟨0, 0, Cantor.zero, Cantor.zero, by omega⟩
  · have h3 : 0 < 3 := by decide
    have hn : 0 < n := Nat.pos_of_ne_zero h0
    have hm := div3_lt n hn
    have ⟨a, b, ha, hb, hab⟩ := cantor_sumset_aux (n / 3)
    have heq : 3 * (n / 3) + n % 3 = n := Nat.div_add_mod n 3
    have hmod : n % 3 < 3 := Nat.mod_lt n h3
    by_cases hr0 : n % 3 = 0
    · exact ⟨3 * a, 3 * b, Cantor.step0 a ha, Cantor.step0 b hb, by omega⟩
    · by_cases hr1 : n % 3 = 1
      · exact ⟨3 * a + 1, 3 * b, Cantor.step1 a ha, Cantor.step0 b hb, by omega⟩
      · have hr2 : n % 3 = 2 := by omega
        exact ⟨3 * a + 1, 3 * b + 1, Cantor.step1 a ha, Cantor.step1 b hb, by omega⟩
termination_by n

/-- **The key theorem (sumset)**: every natural number `n` is a sum `a + b`
where both `a` and `b` are in the Cantor set. This means `A + A = Nat`.

The proof uses strong induction on `n`. For `n = 3 * m + r` with
`r ∈ {0,1,2}`, by IH there exist `a', b'` in the Cantor set with
`a' + b' = m`. Then:
- `r = 0`: take `a = 3a', b = 3b'`, sum = `3(a'+b') = 3m = n`
- `r = 1`: take `a = 3a'+1, b = 3b'`, sum = `3(a'+b')+1 = 3m+1 = n`
- `r = 2`: take `a = 3a'+1, b = 3b'+1`, sum = `3(a'+b')+2 = 3m+2 = n`
Each of `a, b` is in the Cantor set by the constructors. -/
theorem cantor_sumset (n : Nat) :
    ∃ (a : Nat) (b : Nat) (ha : Cantor a) (hb : Cantor b), a + b = n := cantor_sumset_aux n

/-- **Density bound**: at most `2^k` Cantor-set elements below `3^k`.

This shows the Cantor set has natural density 0: the fraction of Cantor
elements below `3^k` is at most `2^k / 3^k = (2/3)^k → 0`. -/
theorem cantor_density_bound (k : Nat) (n : Nat) (h : Cantor n) (hn : n < 3^k) :
    n ∈ cantor_list k ∧ (cantor_list k).length = 2^k := by
  exact ⟨cantor_list_complete n h k hn, cantor_list_length k⟩

end Erdos216
