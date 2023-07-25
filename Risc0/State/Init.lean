import Risc0.State.Defs
import Risc0.State.Validity

namespace Risc0.State

  def empty : State :=
    {
      buffers := Map.empty
      bufferWidths := Map.empty,
      constraints := [],
      cycle := 0, -- should cycle actually equal zero here or should it be arbitrary?
      felts := Map.empty,
      props := Map.empty,
      vars := [],
      isFailed := false,
    }

  def addBuffer (st: State) (name: String) (buffer: Buffer): State :=
    { st with
      buffers := st.buffers[⟨name⟩] ←ₘ buffer,
      bufferWidths := st.bufferWidths[⟨name⟩] ←ₘ buffer.last!.length,
      vars := ⟨name⟩ :: st.vars
    }

  def hasFelts (st: State) (felts: List (String × Felt)) : Prop :=
    match felts with
    | [] => True
    | (name, value) :: fs =>
      st.felts[(⟨name⟩ : FeltVar)]!.get! = value ∧
      st.hasFelts fs

  def init (numInput numOutput : ℕ)
           (input : BufferAtTime) (output : BufferAtTime)
           (_hIn : input.length = numInput) (_hOut : output.length = numOutput) : State where
    buffers      := Map.fromList [(⟨Input⟩, Buffer.init' input), (⟨Output⟩, Buffer.init' output)]
    bufferWidths := Map.fromList [(⟨Input⟩, numInput), (⟨Output⟩, numOutput)]
    constraints  := []
    cycle        := 0
    felts        := Map.empty
    isFailed     := false
    props        := Map.empty
    vars         := [⟨Input⟩, ⟨Output⟩]

  -- Only used to prove State inhabited, since it initialises both input and output as write-only
  def init_default (numInput numOutput : ℕ) : State :=
    init numInput numOutput
          ((Buffer.init numInput).head (by simp [Buffer.init]))
          ((Buffer.init numOutput).head (by simp [Buffer.init]))
          (by simp [Buffer.init])
          (by simp [Buffer.init])

  private lemma valid_init'_aux :
    bufferLensConsistent (State.init m n input output hIn hOut) := λ var h h₁ row h₂ => by
    simp [bufferWidths, init, Buffer.init']
    have : var = ⟨Input⟩ ∨ var = ⟨Output⟩ := by
      unfold init at h; rw [Map.mem_fromList] at h; simp at h; exact h
    have : row = 0 := by simp [init] at h₂; exact h₂
    subst this; simp
    rcases this with h | h <;> subst h <;> simp [Map.update, Map.getElem_def, *]

  lemma valid_init' : (init m n input output hIn hOut).WellFormed where
    distinct := by simp [init]
    hVars    := λ var => ⟨
        λ h => by simp [init] at *; rcases h with h | h <;> subst h ; decide_mem_map,
        λ h => by simp [init] at *; simp [Map.mem_def, Map.update, Map.getElem_def] at h; split at h <;> aesop' 
      ⟩ 
    hCycle   := λ var h => by
      have : var = ⟨Input⟩ ∨ var = ⟨Output⟩ := by
        simp only [init] at h
        rw [Map.mem_fromList] at h
        simp at h
        exact h
      rcases this with h | h <;> subst h <;> simp [Map.getElem_def] <;> rfl
    hCols    := λ var => ⟨
        λ h => by simp [init] at h; rcases h with h | h <;> subst h ; decide_mem_map,
        λ h => by simp [init] at h ⊢; simp [Map.mem_def, Map.update, Map.getElem_def] at h; aesop'
      ⟩ 
    hColsLen := valid_init'_aux

  lemma valid_init : (init_default m n).WellFormed := valid_init'

  instance : Inhabited State := ⟨State.init_default 42 42⟩
end Risc0.State
