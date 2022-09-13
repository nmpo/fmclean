
section propositional

variables P Q R : Prop


------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P  :=
begin
  intro hp,
  intro hnp,
  contradiction,
end

theorem doubleneg_elim :
  ¬¬P → P  :=
begin
  intro hnnp,
  by_cases hnp: P,
    exact hnp,

    have contr := hnnp hnp,
    contradiction,
end

theorem doubleneg_law :
  ¬¬P ↔ P  :=
begin
  split,
  exact doubleneg_elim P,
  exact doubleneg_intro P,
end

------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  :=
begin
  intro disj_pq,
  cases disj_pq,
    right,
      exact disj_pq,
    left,
      exact disj_pq,
end

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  :=
begin
  intro conj_pq,
  cases conj_pq with hp hq,
  split,
    exact hq,    
    exact hp,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos →,∨:
------------------------------------------------

theorem impl_as_disj_converse :
  (¬P ∨ Q) → (P → Q)  :=
begin
  intro disj_pq,
  intro hp,
  cases disj_pq,
    have contr := disj_pq hp,
    contradiction,

    exact disj_pq,
end

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  :=
begin
  intro disj_pq,
  intro hnp,
  cases disj_pq,
    have contr := hnp disj_pq,
    contradiction,

    exact disj_pq,
end


------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  :=
begin
  intro impl_pq,
  intro hnq,
  intro hp,
    have hq := impl_pq hp,
    have contr := hnq hq,
    contradiction,
end

theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  :=
begin
  intro impl_nqnp,
  intro hp,
  by_cases hq: Q,
    exact hq,

    have hnp := impl_nqnp hq,
    have contr := hnp hp,
    contradiction,
end

theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  :=
begin
  split,
  exact impl_as_contrapositive P Q,
  exact impl_as_contrapositive_converse P Q,
end


------------------------------------------------
-- A irrefutabilidade do LEM:
------------------------------------------------

theorem lem_irrefutable :
  ¬¬(P∨¬P)  :=
begin
  intro nlem,
  have lem: P \/ ¬P,
    right,
    intro hp,
    have disj_pnp: P \/ ¬P,
      left,
      exact hp,
    have contr := nlem disj_pnp,
    contradiction,
  have contr := nlem lem,
  contradiction,
end


------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  :=
begin
  intro pq_impl_p,
  intro hnp,
  have impl_pq: P →  Q,
    intro hp,
    contradiction,
  have hp := pq_impl_p impl_pq,
  have contr := hnp hp,
  contradiction,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  :=
begin
  intro disj_pq,
  intro n_conj_npnq,
  cases n_conj_npnq,
  cases disj_pq,
  have contr := n_conj_npnq_left disj_pq,
  contradiction,
  have contr := n_conj_npnq_right disj_pq,
  contradiction,
end

theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  :=
begin
  intro conj_pq,
  intro n_disj_pq,
  cases conj_pq,
  cases n_disj_pq,
  have contr := n_disj_pq conj_pq_left,
  contradiction,
  have contr := n_disj_pq conj_pq_right,
  contradiction,
end


------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_disj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  :=
begin
  intro n_disj_pq,
  split,
    intro hp,

    --intro hq,
end

theorem demorgan_disj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  :=
begin
  intro conj_np_nq,
  intro disj_pq,
  cases disj_pq,
  cases conj_np_nq,
    contradiction,
  cases conj_np_nq,
    contradiction,    
end

theorem demorgan_conj :
  ¬(P∧Q) → (¬Q ∨ ¬P)  :=
begin
  intro n_conj_pq,
  by_cases h: P,
    left,
    intro hq,
    have conj_pq: P /\ Q,
      split,
      exact h,
      exact hq,
    have contr := n_conj_pq conj_pq,
    contradiction,

    right,
    exact h,
end

theorem demorgan_conj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  :=
begin
  intro disj_nq_np,
  intro conj_pq,
  cases conj_pq,
  cases disj_nq_np,
    contradiction,
    contradiction,
end

theorem demorgan_conj_law :
  ¬(P∧Q) ↔ (¬Q ∨ ¬P)  :=
begin
  split,
    exact demorgan_conj P Q,
    exact demorgan_conj_converse P Q,
end

theorem demorgan_disj_law :
  ¬(P∨Q) ↔ (¬P ∧ ¬Q)  :=
begin
  split,
    exact demorgan_disj P Q,
    exact demorgan_disj_converse P Q,
end

------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
------------------------------------------------

theorem distr_conj_disj :
  P∧(Q∨R) → (P∧Q)∨(P∧R)  :=
begin
  intro conj_pdisj,
  cases conj_pdisj with hp disj,
  cases disj with hq hr,
    left,
    split,
      exact hp,
      exact hq,
    right,
    split,
      exact hp,
      exact hr,
end

theorem distr_conj_disj_converse :
  (P∧Q)∨(P∧R) → P∧(Q∨R)  :=
begin
  intro disj_conjs,
  cases disj_conjs with conj_pq conj_pr,
  cases conj_pq with hp hq,
    split,
      exact hp,
      left,
        exact hq,
  cases conj_pr with hp hr,
    split,
    exact hp,
    right,
    exact hr,
end

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
begin
  intro disj_conj_pqr,
  split,
    cases disj_conj_pqr with hp conj_qr,
      left,
        exact hp,
      right,
        cases conj_qr with hq hr,
          exact hq,
    cases disj_conj_pqr with hp conj_qr,
      left,
        exact hp,
      right,
        cases conj_qr with hq hr,
          exact hr,
end

theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  :=
begin
  intro conj_disj,
  cases conj_disj with disj_pq disj_pr,
  cases disj_pq with hp hq,
    left,
      exact hp,
    cases disj_pr with hp hr,
      left,
        exact hp,
      right,
        split,
          exact hq,
          exact hr,
end


------------------------------------------------
-- Currificação
------------------------------------------------

theorem curry_prop :
  ((P∧Q)→R) → (P→(Q→R))  :=
begin
  intro curry,
  intro hp,
  intro hq,

  have conj_pq: P /\ Q,
    split,
      exact hp,
      exact hq,
  
  have R := curry conj_pq,
    exact R,
end

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  :=
begin
  intro uncurry,
  intro conj_pq,
  cases conj_pq with hp hq,
  have implic := uncurry hp,
  have R := implic hq,
  exact R,
end


------------------------------------------------
-- Reflexividade da →:
------------------------------------------------

theorem impl_refl :
  P → P  :=
begin
  intro hp,
  exact hp,
end

------------------------------------------------
-- Weakening and contraction:
------------------------------------------------

theorem weaken_disj_right :
  P → (P∨Q)  :=
begin
  intro hp,
  left,
  exact hp,
end

theorem weaken_disj_left :
  Q → (P∨Q)  :=
begin
  intro hq,
  right,
  exact hq,
end

theorem weaken_conj_right :
  (P∧Q) → P  :=
begin
  intro conj_pq,
  cases conj_pq with hp hq,
  exact hp,
end

theorem weaken_conj_left :
  (P∧Q) → Q  :=
begin
  intro conj_pq,
  cases conj_pq with hp hq,
  exact hq,
end

theorem conj_idempot :
  (P∧P) ↔ P :=
begin
  have theor_left := weaken_conj_left P P,
  split,
    exact theor_left,

    intro hp,
    split,
      exact hp,
      exact hp,
end

theorem disj_idempot :
  (P∨P) ↔ P  :=
begin
  split,
  intro disj_pp,
  cases disj_pp with hp hp,
    exact hp,
    exact hp,
  have theor_right := weaken_disj_left P P,
    exact theor_right,
end

end propositional


----------------------------------------------------------------


section predicate

variable U : Type
variables P Q : U -> Prop


------------------------------------------------
-- As leis de De Morgan para ∃,∀:
------------------------------------------------

theorem demorgan_exists :
  ¬(∃x, P x) → (∀x, ¬P x)  :=
begin
  intro nexist,
  intro hx,
  intro hpx,
  apply nexist,
  existsi hx,
  exact hpx,
end

theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
begin
  intro for_all,
  intro exist,
  cases exist with hx hpx,
  have n_hpx := for_all hx,
  have contr := n_hpx hpx,
  contradiction,
end

theorem demorgan_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  :=
begin
  sorry,
end

theorem demorgan_forall_converse :
  (∃x, ¬P x) → ¬(∀x, P x)  :=
begin
  intro exist,
  intro for_all,
  cases exist with hx hnpx,
  have hpx := for_all hx,
  have contr := hnpx hpx,
  contradiction,
end

theorem demorgan_forall_law :
  ¬(∀x, P x) ↔ (∃x, ¬P x)  :=
begin
  split,
  exact demorgan_forall U P,
  exact demorgan_forall_converse U P,
end

theorem demorgan_exists_law :
  ¬(∃x, P x) ↔ (∀x, ¬P x)  :=
begin
  split,
  exact demorgan_exists U P,
  exact demorgan_exists_converse U P,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∃,∀:
------------------------------------------------

theorem exists_as_neg_forall :
  (∃x, P x) → ¬(∀x, ¬P x)  :=
begin
  intro exist,
  intro for_all,
  cases exist with hx hpx,
  have hnpx := for_all hx,
  have contr := hnpx hpx,
  contradiction,
end

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
begin
  intro for_all,
  intro exist,
  cases exist with hx hnpx,
  have hpx := for_all hx,
  have contr := hnpx hpx,
  contradiction,
end

theorem forall_as_neg_exists_converse :
  ¬(∃x, ¬P x) → (∀x, P x)  :=
begin
  intro n_exist,
  intro hx,
  by_cases P hx,
  exact h,
  have exist: ∃(x: U), ¬P x,
  existsi hx,
  exact h,
  have contr := n_exist exist,
  contradiction,
end

theorem exists_as_neg_forall_converse :
  ¬(∀x, ¬P x) → (∃x, P x)  :=
begin
  sorry,
end

theorem forall_as_neg_exists_law :
  (∀x, P x) ↔ ¬(∃x, ¬P x)  :=
begin
  split,
  exact forall_as_neg_exists U P,
  exact forall_as_neg_exists_converse U P,
end

theorem exists_as_neg_forall_law :
  (∃x, P x) ↔ ¬(∀x, ¬P x)  :=
begin
  split,
  exact exists_as_neg_forall U P,
  exact exists_as_neg_forall_converse U P,
end


------------------------------------------------
--  Proposições de distributividade de quantificadores:
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃x, P x ∧ Q x) → (∃x, P x) ∧ (∃x, Q x)  :=
begin
  sorry,
end

theorem exists_disj_as_disj_exists :
  (∃x, P x ∨ Q x) → (∃x, P x) ∨ (∃x, Q x)  :=
begin
  sorry,
end

theorem exists_disj_as_disj_exists_converse :
  (∃x, P x) ∨ (∃x, Q x) → (∃x, P x ∨ Q x)  :=
begin
  sorry,
end

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  :=
begin
  sorry,
end

theorem forall_conj_as_conj_forall_converse :
  (∀x, P x) ∧ (∀x, Q x) → (∀x, P x ∧ Q x)  :=
begin
  sorry,
end


theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  :=
begin
  sorry,
end


/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
  (∀x, P x ∨ Q x) → (∀x, P x) ∨ (∀x, Q x)  :=
begin
end

theorem exists_conj_as_conj_exists_converse :
  (∃x, P x) ∧ (∃x, Q x) → (∃x, P x ∧ Q x)  :=
begin
end

---------------------------------------------- -/

end predicate
