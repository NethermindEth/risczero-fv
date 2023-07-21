import Risc0.State.Defs

namespace Risc0.State

  def lastOutput (st : State) :=
    st.buffers ⟨Output⟩ |>.get!.getLast!

  def constraintsInVar (st : State) (var : PropVar) :=
    st.props var |>.getD True

end Risc0.State
