ExtensionFunction:=function(Sequence, gonality)
  local posLast, posFirst, incrFirst, incrLast, ListReturn, SC, lfound;
  # find position of last 3
  posLast:=Length(Sequence);
  incrLast:=0;
  while(true)
  do
    if Sequence[posLast]=3 then
      break;
    fi;
    posLast:=posLast-1;
    incrLast:=incrLast+1;
  od;
  # find position of first 3
  posFirst:=1;
  incrFirst:=0;
  while(true)
  do
    if Sequence[posFirst]=3 then
      break;
    fi;
    posFirst:=posFirst+1;
    incrFirst:=incrFirst+1;
  od;
  lfound:=incrFirst+incrLast;
  ListReturn:=[];
  SC:=ShallowCopy(Sequence);
  SC[Length(Sequence)+1]:=3;
  Add(ListReturn, ShallowCopy(SC));
  if lfound< gonality-4 then
    SC[Length(Sequence)+1]:=2;
    Add(ListReturn, ShallowCopy(SC));
  fi;
  return ListReturn;
end;

# gonality should be greater or equal to 5
SearchSimplicicationAndSimplify:=function(Sequence, gonality)
  local iPos, posLast, posFirst, incrLast, incrFirst, lFound, pos, NewSequence;
  for iPos in [1..Length(Sequence)]
  do
    if Sequence[iPos]=2 then
      posLast:=iPos;
      incrLast:=0;
      while(true)
      do
        if Sequence[posLast]=3 then
          break;
        fi;
        posLast:=NextIdx(Length(Sequence), posLast);
        incrLast:=incrLast+1;
      od;
      posFirst:=iPos;
      incrFirst:=0;
      while(true)
      do
        if Sequence[posFirst]=3 then
          break;
        fi;
        posFirst:=PrevIdx(Length(Sequence), posFirst);
        incrFirst:=incrFirst+1;
      od;
      lFound:=incrFirst+incrLast;
      if lFound>gonality-1 then
        return false;
      fi;
      if lFound> gonality-3 then
        NewSequence:=[];
        if lFound=gonality-2 then
          Add(NewSequence, [3]);
        fi;
        pos:=posLast;
        while(true)
        do
          if pos=posLast or pos=posFirst then
            Add(NewSequence, [2]);
          else
            Add(NewSequence, Sequence[pos]);
          fi;
          if pos=posFirst then
            break;
          fi;
          pos:=pos+1;
        od;
        return NewSequence;
      fi;
    fi;
  od;
  # no simplification found
  return Sequence;
end;

TrivialSimplification:=function(Sequence, gonality)
  local Seq1, FinishSequence, i, Seq2;
  Seq1:=ShallowCopy(Sequence);
  FinishSequence:=[];
  for i in [1..gonality]
  do
    Add(FinishSequence, [2]);
  od;
  while(true)
  do
    if Seq1=FinishSequence then
      return [];
    fi;
    Seq2:=SearchSimplicicationAndSimplify(Seq1, gonality);
    if Seq2=false then
      return false;
    fi;
    if Seq2=Seq1 then
      return Seq2;
    else
      Seq1:=Seq2;
    fi;
  od;
end;

CompletionOneEdge:=function(REQ, iPos1, iPos2)
  local SEQ, MAP, GRA, SEQnew, MAPnew, pos, Granew, iVert, jVert;
  SEQ:=REQ.SEQ;
  MAP:=REQ.MAP;
  GRA:=REQ.GRA;
  SEQnew:=[3,3];
  MAPnew:=[MAP[iPos1], MAP[iPos2]];
  pos:=NextIdx(Length(SEQ), iPos2);
  while(true)
  do
    Add(SEQnew, SEQ[pos]);
    Add(MAPnew, MAP[pos]);
    pos:=NextIdx(Length(SEQ), pos);
    if iPos1=pos then
      break;
    fi;
  od;
  Granew:=NullGraph(Group(()), GRA.order);
  for iVert in [1..GRA.order-1]
  do
    for jVert in [iVert+1..GRA.order]
    do
      if IsEdge(GRA, [iVert, jVert])=true then
        AddEdgeOrbit(Granew, [iVert, jVert]);
        AddEdgeOrbit(Granew, [jVert, iVert]);
      fi;
    od;
  od;
  AddEdgeOrbit(Granew, [MAP[iPos1], MAP[iPos2]]);
  AddEdgeOrbit(Granew, [MAP[iPos2], MAP[iPos1]]);
  return rec(SEQ:=SEQnew, MAP:=MAPnew, GRA:=Granew);
end;

CompletionTwoEdgeOneVertex:=function(REQ, iPos1, iPos2)
  local SEQ, MAP, GRA, SEQnew, MAPnew, pos, Granew, iVert, jVert, LV, u;
  SEQ:=REQ.SEQ;
  MAP:=REQ.MAP;
  GRA:=REQ.GRA;
  SEQnew:=[3,2,3];
  MAPnew:=[MAP[iPos1], GRA.order+1, MAP[iPos2]];
  pos:=NextIdx(Length(SEQ), iPos2);
  while(true)
  do
    Add(SEQnew, SEQ[pos]);
    Add(MAPnew, MAP[pos]);
    pos:=NextIdx(Length(SEQ), pos);
    if iPos1=pos then
      break;
    fi;
  od;
  Granew:=NullGraph(Group(()), GRA.order+1);
  for iVert in [1..GRA.order-1]
  do
    for jVert in [iVert+1..GRA.order]
    do
      if IsEdge(GRA, [iVert, jVert])=true then
        AddEdgeOrbit(Granew, [iVert, jVert]);
        AddEdgeOrbit(Granew, [jVert, iVert]);
      fi;
    od;
  od;
  LV:=[MAP[iPos1], GRA.order+1, MAP[iPos2]];
  for u in [1..2]
  do
    AddEdgeOrbit(Granew, [LV[u], LV[u+1]]);
    AddEdgeOrbit(Granew, [LV[u+1], LV[u]]);
  od;
  return rec(SEQ:=SEQnew, MAP:=MAPnew, GRA:=Granew);
end;

SaturationPgonPatch:=function(REQ, Cycle, P)
  local REQwork, FuncFind, PP, reply;
  FuncFind:=function()
    local i, idx1, idx2;
    for i in [1..Length(REQwork.SEQ)]
    do
      idx1:=i;
      idx2:=NextIdx(Length(REQwork.SEQ), idx1);
      if Position(Cycle, REQwork.MAP[idx1])<>fail and Position(Cycle, REQwork.MAP[idx2])<>fail then
        while(true)
        do
          if REQwork.SEQ[idx1]=2 then
            break;
          fi;
          idx1:=PrevIdx(Length(REQwork.SEQ), idx1);
        od;
        while(true)
        do
          if REQwork.SEQ[idx2]=2 then
            break;
          fi;
          idx2:=NextIdx(Length(REQwork.SEQ), idx2);
        od;
        return [idx1, idx2];
      fi;
    od;
    return fail;
  end;
  REQwork:=ShallowCopy(REQ);
  while(true)
  do
    PP:=FuncFind();
    if PP=fail then
      break;
    fi;
    Print("PP1=", PP[1], "   PP2=", PP[2], "\n");
    reply:=CompletionPgon(REQwork, PP[1], PP[2], P);
    if reply=false then
      return false;
    fi;
    REQwork:=reply[1];
  od;  
  return REQwork;
end;


