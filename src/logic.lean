
section propositional

variables P Q R : Prop


------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P  :=
begin
  intro P,
  contradiction,
end

theorem doubleneg_elim :
  ¬¬P → P  :=
begin
  intro H,
  by_contradiction hboom,
  contradiction,

end

theorem doubleneg_law :
  ¬¬P ↔ P  :=
begin
  split,
  intro H,
  by_contradiction hboom,
  contradiction,
  intro P,
  contradiction,
end

------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  :=
begin
  intro H,
  cases H with hp hq,
  right,
  exact hp,
  left,
  exact hq,
end

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  :=
begin
  intro H,
  cases H with hp hq,
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
  intro H,
  intro P,
  cases H with hb hq,
  contradiction,
  exact hq,
end

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  :=
begin
  intro H,
  intro I,
  cases H with hp hq,
  contradiction,
  exact hq,
end


------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  :=
begin
  intro H,
  intro W,
  intro G,
  have J : Q := H G,
  apply W,
  exact J,
end

theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  :=
begin
  intro H,
  intro P,
  by_contra hboom,
  apply H,
  exact hboom,
  exact P,
end

theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  :=
begin
  split,
  intro H,
  intro W,
  intro G,
  have J : Q := H G,
  apply W,
  exact J,
  intro H,
  intro P,
  by_contra hboom,
  apply H,
  exact hboom,
  exact P,
end


------------------------------------------------
-- A irrefutabilidade do LEM:
------------------------------------------------

theorem lem_irrefutable :
  ¬¬(P∨¬P)  :=
begin
  intro H,
  have h : P∨¬P,
  right,
  intro G,
  have g : P∨¬P,
  left,
  exact G,
  contradiction,
  contradiction,
end


------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  :=
begin
  intro H,
  intro G,
  have g : (¬P ∨ Q) → (P → Q),
  intro J,
  intro p,
  cases J with hj hq,
  contradiction,
  exact hq,
  have h : ¬P ∨ Q,
  left,
  exact G,
  have hpq : P → Q := g h,
  have p : P := H hpq,
  contradiction,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  :=
begin
  intro H,
  intro G,
  cases G with hp hq,
  cases H with P Q,
  apply hp,
  exact P,
  apply hq,
  exact Q,
end

theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  :=
begin
  intro H,
  intro G,
  cases H with P Q,
  cases G with hp hq,
  apply hp,
  exact P,
  apply hq,
  exact Q,
end


------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_disj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  :=
begin
  intro H,
  split,
  intro hp,
  have hpq : P∨Q,
  left,
  exact hp,
  contradiction,
  intro hq,
  have hpq : P∨Q,
  right,
  exact hq,
  contradiction,
end

theorem demorgan_disj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  :=
begin
  intro H,
  intro G,
  cases H with ho hw,
  cases G with hp hq,
  apply ho,
  exact hp,
  apply hw,
  exact hq,
end

theorem demorgan_conj :
  ¬(P∧Q) → (¬Q ∨ ¬P)  :=
begin
  intro H,
  by_cases h : P,
  left,
  intro G,
  have j : P∧Q,
  split,
  exact h,
  exact G,
  apply H,
  exact j,
  right,
  exact h,

end

theorem demorgan_conj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  :=
begin
  intro H,
  intro G,
  cases G with hp hq,
  cases H with hw ho,
  apply hw,
  exact hq,
  apply ho,
  exact hp,
end

theorem demorgan_conj_law :
  ¬(P∧Q) ↔ (¬Q ∨ ¬P)  :=
begin
  split,
  intro H,
  by_cases h : P,
  left,
  intro G,
  have j : P∧Q,
  split,
  exact h,
  exact G,
  apply H,
  exact j,
  right,
  exact h,
  intro H,
  intro G,
  cases G with hp hq,
  cases H with hw ho,
  apply hw,
  exact hq,
  apply ho,
  exact hp,
end

theorem demorgan_disj_law :
  ¬(P∨Q) ↔ (¬P ∧ ¬Q)  :=
begin
  split,
  intro H,
  split,
  intro hp,
  have hpq : P∨Q,
  left,
  exact hp,
  contradiction,
  intro hq,
  have hpq : P∨Q,
  right,
  exact hq,
  contradiction,
  intro H,
  intro G,
  cases H with ho hw,
  cases G with hp hq,
  apply ho,
  exact hp,
  apply hw,
  exact hq,
end

------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
------------------------------------------------

theorem distr_conj_disj :
  P∧(Q∨R) → (P∧Q)∨(P∧R)  :=
begin
  intro H,
  cases H with hp hqr,
  cases hqr with hq hr,
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
  intro H,
  split,
  cases H with hpq hpr,
  cases hpq with hp hq,
  exact hp,
  cases hpr with hp hr,
  exact hp,
  cases H with hpq hpr,
  left,
  cases hpq with hp hq,
  exact hq,
  right,
  cases hpr with hp hr,
  exact hr,
end

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
begin
  intro H,
  split,
  cases H with hp hqr,
  left,
  exact hp,
  right,
  cases hqr with hq hr,
  exact hq,
  cases H with hp hqr,
  left,
  exact hp,
  right,
  cases hqr with hq hr,
  exact hr,
end

theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  :=
begin
  intro H,
  cases H with hpq hpr,
  cases hpq with hp hq,
  left,
  exact hp,
  cases hpr with hp hr,
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
  intro H,
  intro hp,
  intro hq,
  have h : P∧Q,
  split,
  exact hp,
  exact hq,
  apply H,
  exact h,
end

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  :=
begin
  intro H,
  intro G,
  cases G with hp hq,
  have hqr : Q→R := H hp,
  apply hqr,
  exact hq,
end


------------------------------------------------
-- Reflexividade da →:
------------------------------------------------

theorem impl_refl :
  P → P  :=
begin
  intro H,
  exact H,
end

------------------------------------------------
-- Weakening and contraction:
------------------------------------------------

theorem weaken_disj_right :
  P → (P∨Q)  :=
begin
  intro H,
  left,
  exact H,
end

theorem weaken_disj_left :
  Q → (P∨Q)  :=
begin
  intro H,
  right,
  exact H,
end

theorem weaken_conj_right :
  (P∧Q) → P  :=
begin
  intro H,
  cases H with hp hq,
  exact hp,
end

theorem weaken_conj_left :
  (P∧Q) → Q  :=
begin
  intro H,
  cases H with hp hq,
  exact hq,
end

theorem conj_idempot :
  (P∧P) ↔ P :=
begin
  split,
  intro H,
  cases H with hp hq,
  exact hp,
  intro H,
  split,
  exact H, 
  exact H,
end

theorem disj_idempot :
  (P∨P) ↔ P  :=
begin
  split,
  intro H,
  cases H with hp1 hp2,
  exact hp1,
  exact hp2,
  intro H,
  left,
  exact H,
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
  intro H,
  intro a,
  intro b,
  apply H,
  existsi a,
  exact b,
end

theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
begin
  intro H,
  intro G,
  cases G with a G_h,
  apply H,
  exact G_h,
end

theorem demorgan_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  :=
begin
  intro H,
  by_contra hboom,
  have h : ∀x, P x,
  intro a,
  by_cases h : P a,
  exact h,
  have G : ∃x, ¬P x,
  existsi a,
  exact h,
  contradiction,
  contradiction,
end

theorem demorgan_forall_converse :
  (∃x, ¬P x) → ¬(∀x, P x)  :=
begin
  intro H,
  intro G,
  cases H with a H_g,
  have hp : P a := G a,
  apply H_g,
  exact hp,
end

theorem demorgan_forall_law :
  ¬(∀x, P x) ↔ (∃x, ¬P x)  :=
begin
  split,
  intro H,
  by_contra hboom,
  have h : ∀x, P x,
  intro a,
  by_cases h : P a,
  exact h,
  have G : ∃x, ¬P x,
  existsi a,
  exact h,
  contradiction,
  contradiction,
  intro H,
  intro G,
  cases H with a H_g,
  have hp : P a := G a,
  apply H_g,
  exact hp,
end

theorem demorgan_exists_law :
  ¬(∃x, P x) ↔ (∀x, ¬P x)  :=
begin
  split,
  intro H,
  intro a,
  intro b,
  apply H,
  existsi a,
  exact b,
  intro H,
  intro G,
  cases G with a G_h,
  apply H,
  exact G_h,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∃,∀:
------------------------------------------------

theorem exists_as_neg_forall :
  (∃x, P x) → ¬(∀x, ¬P x)  :=
begin
  intro H,
  intro G,
  cases H with a H_a,
  apply G,
  exact H_a,
end

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
begin
  intro H,
  intro G,
  cases G with a G_a,
  have H_a : P a := H a,
  apply G_a,
  exact H_a,
end

theorem forall_as_neg_exists_converse :
  ¬(∃x, ¬P x) → (∀x, P x)  :=
begin
  intro H,
  intro a,
  by_cases h : P a,
  exact h,
  have G : ∃x, ¬P x,
  existsi a,
  exact h,
  contradiction,
end

theorem exists_as_neg_forall_converse :
  ¬(∀x, ¬P x) → (∃x, P x)  :=
begin
  intro H,
  by_contra hboom,
  have h : ∀x, ¬P x,
  intro a,
  intro G,
  apply hboom,
  existsi a,
  exact G,
  contradiction,
end

theorem forall_as_neg_exists_law :
  (∀x, P x) ↔ ¬(∃x, ¬P x)  :=
begin
  split,
  intro H,
  intro G,
  cases G with a G_a,
  have H_a : P a := H a,
  apply G_a,
  exact H_a,
  intro H,
  intro a,
  by_contra hboom,
  apply H,
  existsi a,
  exact hboom,
end

theorem exists_as_neg_forall_law :
  (∃x, P x) ↔ ¬(∀x, ¬P x)  :=
begin
  split,
  intro H,
  intro G,
  cases H with a H_a,
  apply G,
  exact H_a,
  intro H,
  by_contra hboom,
  have h : ∀x, ¬P x,
  intro a,
  intro G,
  apply hboom,
  existsi a,
  exact G,
  contradiction,
end


------------------------------------------------
--  Proposições de distributividade de quantificadores:
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃x, P x ∧ Q x) → (∃x, P x) ∧ (∃x, Q x)  :=
begin
  intro H,
  cases H with a hpq,
  cases hpq with hp hq,
  split,
  existsi a,
  exact hp,
  existsi a,
  exact hq,
end

theorem exists_disj_as_disj_exists :
  (∃x, P x ∨ Q x) → (∃x, P x) ∨ (∃x, Q x)  :=
begin
  intro H,
  cases H with a hpq,
  cases hpq with hp hq,
  left,
  existsi a,
  exact hp,
  right,
  existsi a,
  exact hq,
end

theorem exists_disj_as_disj_exists_converse :
  (∃x, P x) ∨ (∃x, Q x) → (∃x, P x ∨ Q x)  :=
begin
  intro H,
  cases H with hp hq,
  cases hp with a hp_a,
  existsi a,
  left,
  exact hp_a,
  cases hq with a hq_a,
   existsi a,
  right,
  exact hq_a,
end

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  :=
begin
  intro H,
  split,
  intro a,
  have hpq : P a ∧ Q a := H a,
  cases hpq with hp hq,
  exact hp,
  intro b,
  have hpq : P b ∧ Q b := H b,
  cases hpq with hp hq,
  exact hq,
end

theorem forall_conj_as_conj_forall_converse :
  (∀x, P x) ∧ (∀x, Q x) → (∀x, P x ∧ Q x)  :=
begin
  intro H,
  intro a,
  cases H with hp hq,
  split,
  apply hp,
  apply hq,
end


theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  :=
begin
  intro H,
  intro a,
  cases H with hp hq,
  left,
  apply hp,
  right,
  apply hq,
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
