import Risc0.BasicTypes
import Risc0.Cirgen
import Risc0.CompoundTypes
import Risc0.Lemmas
import Risc0.Map
import Risc0.MlirTactics
import Risc0.Optimisation
import Risc0.Wheels

import Risc0.Gadgets.OneHot20.Witness.Code
import Risc0.Gadgets.OneHot20.Constraints.Code
import Risc0.Gadgets.OneHot20.Constraints.CodeReordered
import Risc0.Gadgets.OneHot20.Witness.CodeReordered
import Risc0.Gadgets.OneHot20.Constraints.CodeParts
import Risc0.Gadgets.OneHot20.Witness.CodeParts
import Risc0.Gadgets.OneHot20.Constraints.CodeDrops
import Risc0.Gadgets.OneHot20.Witness.CodeDrops
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart0
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart1
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart2
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart3
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart4
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart5
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart6
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart7
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart8
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart9
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart10
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart11
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart12
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart13
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart14
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart15
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart16
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart17
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart18
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart19
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart20
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart21
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart22
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart23
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart24
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart25
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart26
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart27
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart28
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart29
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart30
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart31
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart32
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart33
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart34
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart35
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart36
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart37
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart38
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart39
import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart0
import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart1
import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart2
import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart3
-- import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart4
-- import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart5
-- import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart6
-- import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart7
-- import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart8
-- import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart9
-- import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart10
-- import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart11
-- import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart12
-- import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart13
-- import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart14
-- import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart15
-- import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart16
-- import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart17
-- import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart18
-- import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart19
-- import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart20
-- import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart21
-- import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart22
-- import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart23
-- import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart24
-- import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart25
-- import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart26
-- import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart27
-- import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart28
-- import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart29
-- import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart30
-- import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart31
-- import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart32
-- import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart33
-- import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart34
-- import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart35
-- import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart36
-- import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart37
-- import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart38
-- import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart39
-- import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart40
-- import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart41
-- import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart42
-- import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart43
-- import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart44
-- import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart45
-- import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart46
-- import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart47
-- import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart48
-- import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart49
-- import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart50
-- import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart51
-- import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart52
-- import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart53
-- import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart54

import Risc0.Gadgets.IsZero.Witness.Code
import Risc0.Gadgets.IsZero.Constraints.Code
import Risc0.Gadgets.IsZero.Constraints.CodeReordered
import Risc0.Gadgets.IsZero.Witness.CodeReordered
import Risc0.Gadgets.IsZero.Constraints.CodeParts
import Risc0.Gadgets.IsZero.Witness.CodeParts
import Risc0.Gadgets.IsZero.Constraints.CodeDrops
import Risc0.Gadgets.IsZero.Witness.CodeDrops
import Risc0.Gadgets.IsZero.Constraints.WeakestPresPart0
import Risc0.Gadgets.IsZero.Constraints.WeakestPresPart1
import Risc0.Gadgets.IsZero.Constraints.WeakestPresPart2
import Risc0.Gadgets.IsZero.Witness.WeakestPresPart0
import Risc0.Gadgets.IsZero.Witness.WeakestPresPart1
import Risc0.Gadgets.IsZero.Witness.WeakestPresPart2
-- import Risc0.Gadgets.IsZero.Proofs

-- import Risc0.Gadgets.ComputeDecode.Witness.Code
-- import Risc0.Gadgets.ComputeDecode.Constraints.Code
-- import Risc0.Gadgets.ComputeDecode.Constraints.CodeReordered
-- import Risc0.Gadgets.ComputeDecode.Witness.CodeReordered
-- import Risc0.Gadgets.ComputeDecode.Constraints.CodeParts
-- import Risc0.Gadgets.ComputeDecode.Witness.CodeParts
-- import Risc0.Gadgets.ComputeDecode.Constraints.CodeDrops
-- import Risc0.Gadgets.ComputeDecode.Witness.CodeDrops
-- import Risc0.Gadgets.ComputeDecode.Constraints.WeakestPresPart0
-- import Risc0.Gadgets.ComputeDecode.Constraints.WeakestPresPart1
-- import Risc0.Gadgets.ComputeDecode.Constraints.WeakestPresPart2
-- import Risc0.Gadgets.ComputeDecode.Constraints.WeakestPresPart3
-- import Risc0.Gadgets.ComputeDecode.Constraints.WeakestPresPart4
-- import Risc0.Gadgets.ComputeDecode.Constraints.WeakestPresPart5
-- import Risc0.Gadgets.ComputeDecode.Constraints.WeakestPresPart6
-- import Risc0.Gadgets.ComputeDecode.Constraints.WeakestPresPart7
-- import Risc0.Gadgets.ComputeDecode.Constraints.WeakestPresPart8
-- import Risc0.Gadgets.ComputeDecode.Constraints.WeakestPresPart9
-- import Risc0.Gadgets.ComputeDecode.Constraints.WeakestPresPart10
-- import Risc0.Gadgets.ComputeDecode.Constraints.WeakestPresPart11
-- import Risc0.Gadgets.ComputeDecode.Constraints.WeakestPresPart12
-- import Risc0.Gadgets.ComputeDecode.Constraints.WeakestPresPart13
-- import Risc0.Gadgets.ComputeDecode.Constraints.WeakestPresPart14
-- import Risc0.Gadgets.ComputeDecode.Constraints.WeakestPresPart15
-- import Risc0.Gadgets.ComputeDecode.Constraints.WeakestPresPart16
-- import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart0
-- import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart1
-- import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart2
-- import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart3
-- import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart4
-- import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart5
-- import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart6
-- import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart7
-- import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart8
-- import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart9
-- import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart10
-- import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart11
-- import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart12
-- import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart13
-- import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart14
-- import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart15
-- import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart16
-- import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart17
-- import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart18
-- import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart19
-- import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart20
-- import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart21
-- import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart22
-- import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart23
-- import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart24
-- import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart25
-- import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart26
-- import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart27
-- import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart28
-- import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart29
-- import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart30
-- import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart31

import Risc0.Gadgets.OneHot2.Witness.Code
import Risc0.Gadgets.OneHot2.Constraints.Code
import Risc0.Gadgets.OneHot2.Constraints.CodeReordered
import Risc0.Gadgets.OneHot2.Witness.CodeReordered
import Risc0.Gadgets.OneHot2.Constraints.CodeParts
import Risc0.Gadgets.OneHot2.Witness.CodeParts
import Risc0.Gadgets.OneHot2.Constraints.CodeDrops
import Risc0.Gadgets.OneHot2.Witness.CodeDrops
import Risc0.Gadgets.OneHot2.Constraints.WeakestPresPart0
import Risc0.Gadgets.OneHot2.Constraints.WeakestPresPart1
import Risc0.Gadgets.OneHot2.Constraints.WeakestPresPart2
import Risc0.Gadgets.OneHot2.Constraints.WeakestPresPart3
import Risc0.Gadgets.OneHot2.Witness.WeakestPresPart0
import Risc0.Gadgets.OneHot2.Witness.WeakestPresPart1
import Risc0.Gadgets.OneHot2.Witness.WeakestPresPart2
import Risc0.Gadgets.OneHot2.Witness.WeakestPresPart3
import Risc0.Gadgets.OneHot2.Witness.WeakestPresPart4
import Risc0.Gadgets.OneHot2.Witness.WeakestPresPart5
-- import Risc0.Gadgets.OneHot2.Proofs

import Risc0.Gadgets.OneHot1.Witness.Code
import Risc0.Gadgets.OneHot1.Constraints.Code
import Risc0.Gadgets.OneHot1.Constraints.CodeReordered
import Risc0.Gadgets.OneHot1.Witness.CodeReordered
import Risc0.Gadgets.OneHot1.Constraints.CodeParts
import Risc0.Gadgets.OneHot1.Witness.CodeParts
import Risc0.Gadgets.OneHot1.Constraints.CodeDrops
import Risc0.Gadgets.OneHot1.Witness.CodeDrops
import Risc0.Gadgets.OneHot1.Constraints.WeakestPresPart0
import Risc0.Gadgets.OneHot1.Constraints.WeakestPresPart1
import Risc0.Gadgets.OneHot1.Constraints.WeakestPresPart2
import Risc0.Gadgets.OneHot1.Witness.WeakestPresPart0
import Risc0.Gadgets.OneHot1.Witness.WeakestPresPart1
import Risc0.Gadgets.OneHot1.Witness.WeakestPresPart2
import Risc0.Gadgets.OneHot1.Witness.WeakestPresPart3
import Risc0.Gadgets.computeDecode.Witness.Code
import Risc0.Gadgets.computeDecode.Constraints.Code
import Risc0.Gadgets.computeDecode.Constraints.CodeReordered
import Risc0.Gadgets.computeDecode.Witness.CodeReordered
import Risc0.Gadgets.computeDecode.Constraints.CodeParts
import Risc0.Gadgets.computeDecode.Witness.CodeParts
import Risc0.Gadgets.computeDecode.Constraints.CodeDrops
import Risc0.Gadgets.computeDecode.Witness.CodeDrops
import Risc0.Gadgets.computeDecode.Constraints.WeakestPresPart0
import Risc0.Gadgets.computeDecode.Constraints.WeakestPresPart1
import Risc0.Gadgets.computeDecode.Constraints.WeakestPresPart2
import Risc0.Gadgets.computeDecode.Constraints.WeakestPresPart3
import Risc0.Gadgets.computeDecode.Constraints.WeakestPresPart4
import Risc0.Gadgets.computeDecode.Constraints.WeakestPresPart5
import Risc0.Gadgets.computeDecode.Constraints.WeakestPresPart6
import Risc0.Gadgets.computeDecode.Constraints.WeakestPresPart7
import Risc0.Gadgets.computeDecode.Constraints.WeakestPresPart8
import Risc0.Gadgets.computeDecode.Constraints.WeakestPresPart9
import Risc0.Gadgets.computeDecode.Constraints.WeakestPresPart10
import Risc0.Gadgets.computeDecode.Constraints.WeakestPresPart11
import Risc0.Gadgets.computeDecode.Constraints.WeakestPresPart12
import Risc0.Gadgets.computeDecode.Constraints.WeakestPresPart13
import Risc0.Gadgets.computeDecode.Constraints.WeakestPresPart14
import Risc0.Gadgets.computeDecode.Constraints.WeakestPresPart15
import Risc0.Gadgets.computeDecode.Witness.WeakestPresPart0
import Risc0.Gadgets.computeDecode.Witness.WeakestPresPart1
import Risc0.Gadgets.computeDecode.Witness.WeakestPresPart2
import Risc0.Gadgets.computeDecode.Witness.WeakestPresPart3
import Risc0.Gadgets.computeDecode.Witness.WeakestPresPart4
import Risc0.Gadgets.computeDecode.Witness.WeakestPresPart5
import Risc0.Gadgets.computeDecode.Witness.WeakestPresPart6
import Risc0.Gadgets.computeDecode.Witness.WeakestPresPart7
import Risc0.Gadgets.computeDecode.Witness.WeakestPresPart8
import Risc0.Gadgets.computeDecode.Witness.WeakestPresPart9
import Risc0.Gadgets.computeDecode.Witness.WeakestPresPart10
import Risc0.Gadgets.computeDecode.Witness.WeakestPresPart11
import Risc0.Gadgets.computeDecode.Witness.WeakestPresPart12
import Risc0.Gadgets.computeDecode.Witness.WeakestPresPart13
import Risc0.Gadgets.computeDecode.Witness.WeakestPresPart14
import Risc0.Gadgets.computeDecode.Witness.WeakestPresPart15
import Risc0.Gadgets.computeDecode.Witness.WeakestPresPart16
import Risc0.Gadgets.computeDecode.Witness.WeakestPresPart17
import Risc0.Gadgets.computeDecode.Witness.WeakestPresPart18
import Risc0.Gadgets.computeDecode.Witness.WeakestPresPart19
import Risc0.Gadgets.computeDecode.Witness.WeakestPresPart20