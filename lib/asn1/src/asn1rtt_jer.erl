%%
%% %CopyrightBegin%
%%
%% Copyright Ericsson AB 2012-2017. All Rights Reserved.
%%
%% Licensed under the Apache License, Version 2.0 (the "License");
%% you may not use this file except in compliance with the License.
%% You may obtain a copy of the License at
%%
%%     http://www.apache.org/licenses/LICENSE-2.0
%%
%% Unless required by applicable law or agreed to in writing, software
%% distributed under the License is distributed on an "AS IS" BASIS,
%% WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
%% See the License for the specific language governing permissions and
%% limitations under the License.
%%
%% %CopyrightEnd%
%%

-module(asn1rtt_jer).
%% encoding / decoding of BER
-ifdef(DEBUG).
-compile(export_all).
-endif.
%% For typeinfo JER
-export([encode_jer/3, decode_jer/3]).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Common code for all JER encoding/decoding
%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
encode_jer(Module,InfoFunc,Val) ->
    Info = Module:InfoFunc(),
    encode_jer(Info,Val).

encode_jer({sequence,Sname,Arity,CompInfos},Value) 
  when tuple_size(Value) == Arity+1 ->
    [Sname|Clist] = tuple_to_list(Value),
    encode_jer_component(CompInfos,Clist,#{});
encode_jer(string,Str) when is_list(Str) ->
    list_to_binary(Str);
encode_jer({string,_Prop},Str) when is_list(Str) ->
    list_to_binary(Str);
encode_jer(string,Str) when is_binary(Str) ->
    Str;
encode_jer({string,_Prop},Str) when is_binary(Str) ->
    Str;
encode_jer('INTEGER',Int) when is_integer(Int) ->
    Int;
encode_jer({'INTEGER',_Prop},Int) when is_integer(Int) ->
    Int;
encode_jer('BOOLEAN',Bool) when is_boolean(Bool) ->
    Bool;
encode_jer({'BOOLEAN',_Prop},Bool) when is_boolean(Bool) ->
    Bool;
encode_jer('NULL','NULL') ->
    null;
encode_jer(legacy_octet_string, Value) when is_list(Value) ->
    bitstring2json(list_to_binary(Value));
encode_jer({legacy_octet_string,_Prop}, Value) when is_list(Value) ->
    bitstring2json(list_to_binary(Value));
encode_jer(octet_string,Value) when is_binary(Value) ->
    encode_jer({octet_string,[]}, Value);
encode_jer({octet_string,_Prop}, Value) when is_binary(Value) ->
    bitstring2json(Value);

%% FIXME, should maybe represent EnumList as a Map and 
%% check if Val is one of the allowed ones
encode_jer({'ENUMERATED',_EnumList},Val) when is_atom(Val) ->
    Val;
encode_jer({typeinfo,{Module,Func}},Val) ->
    TypeInfo = Module:Func(),
    encode_jer(TypeInfo,Val);
 
encode_jer({sof,Type},Vals) when is_list(Vals) ->
    [encode_jer(Type,Val)||Val <- Vals];
encode_jer({choice,Choices},{Alt,Value}) ->
    case is_map_key(AltBin = atom_to_binary(Alt,utf8),Choices) of
        true ->
            EncodedVal = encode_jer(maps:get(AltBin,Choices),Value),
            #{AltBin => EncodedVal};
        false ->
            exit({error,{asn1,{invalid_choice,Alt,Choices}}})
    end;
    
encode_jer(bit_string,Value) ->
    Str = bitstring2json(Value),
    #{value => Str, length => bit_size(Value)};
encode_jer({bit_string,FixedLength},Value) when is_bitstring(Value), is_integer(FixedLength) ->
    FixedLength = bit_size(Value), % assertion that must hold 
    bitstring2json(Value);
encode_jer(compact_bit_string,{Unused,Binary}) when is_binary(Binary) ->
    Size = bit_size(Binary) - Unused,
    <<BitStr:Size/bitstring,_/bitstring >> = Binary, 
    encode_jer(bit_string,BitStr);

encode_jer({compact_bit_string,FixedLength},{Unused,Binary}) when is_binary(Binary) ->
    Size = bit_size(Binary) - Unused,
    FixedLength = Size, % assertion that must hold otherwise faulty input
    <<BitStr:Size/bitstring,_/bitstring >> = Binary, 
    encode_jer({bit_string,FixedLength},BitStr).

encode_jer_component([_|CompInfos],[asn1_NOVALUE|Rest],MapAcc) ->
    encode_jer_component(CompInfos,Rest,MapAcc);
encode_jer_component([{Name,Type}|CompInfos],[Value|Rest],MapAcc) ->
    Enc = encode_jer(Type,Value),
    encode_jer_component(CompInfos,Rest,MapAcc#{Name=>Enc});
encode_jer_component([],_,MapAcc) ->
    MapAcc.

decode_jer(Module,InfoFunc,Val) ->
    Info = Module:InfoFunc(),
    decode_jer(Info,Val).
%% FIXME probably generate EnumList as a map with binaries as keys
%% and check if the Value is in the map. Also take the extensionmarker into
%% account and in that case allow any value but return as binary since it
%% is a potential atom leak to convert unknown values to atoms
%% maybe convert to existing atom
decode_jer({'ENUMERATED',_EnumList}, Val) when is_binary(Val) ->
    binary_to_existing_atom(Val,utf8);
decode_jer({'ENUMERATED',_EnumList}, Val) when is_boolean(Val) ->
    Val;
decode_jer({'ENUMERATED',_EnumList}, null) ->
    null;
decode_jer({typeinfo,{Module,Func}},Val) ->
    TypeInfo = Module:Func(),
    decode_jer(TypeInfo,Val); 
decode_jer({sequence,Sname,_Arity,CompInfos},Value) 
  when is_map(Value) ->    
    DecodedComps = decode_jer_component(CompInfos,Value,[]),
    list_to_tuple([Sname|DecodedComps]);
decode_jer(string,Str) when is_binary(Str) ->
    Str;
decode_jer({string,_Prop},Str) when is_binary(Str) ->
    Str;
decode_jer('INTEGER',Int) when is_integer(Int) ->
    Int;
decode_jer({'INTEGER',_Prop},Int) when is_integer(Int) ->
    Int;
decode_jer('BOOLEAN',Bool) when is_boolean(Bool) ->
    Bool;
decode_jer({'BOOLEAN',_Prop},Bool) when is_boolean(Bool) ->
    Bool;
decode_jer('NULL',null) ->
    'NULL';
decode_jer(legacy_octet_string,Str) when is_binary(Str) ->
    json2octetstring2string(binary_to_list(Str));
decode_jer(octet_string,Str) when is_binary(Str) ->
    json2octetstring2binary(binary_to_list(Str));
decode_jer({sof,Type},Vals) when is_list(Vals) ->
    [decode_jer(Type,Val)||Val <- Vals];
decode_jer({choice,ChoiceTypes},ChoiceVal) ->
    [{Alt,Val}] = maps:to_list(ChoiceVal),
    case ChoiceTypes of
        #{Alt := Type} ->
            Type = maps:get(Alt,ChoiceTypes),
            {binary_to_atom(Alt,utf8),decode_jer(Type,Val)};
        _ ->
            exit({error,{asn1,{invalid_choice,Alt,maps:keys(ChoiceTypes)}}})
    end;
decode_jer(bit_string,#{<<"value">> := Str, <<"length">> := Length}) ->
    json2bitstring(binary_to_list(Str),Length);
decode_jer({bit_string,FixedLength},Str) when is_binary(Str) ->
    json2bitstring(binary_to_list(Str),FixedLength);
decode_jer(compact_bit_string,#{<<"value">> := Str, <<"length">> := Length}) ->
    BitStr = json2bitstring(binary_to_list(Str),Length),
    Unused = (8 - (Length rem 8)) band 7,
    {Unused,<<BitStr/bitstring,0:Unused>>};
decode_jer({compact_bit_string,FixedLength},Str) ->
    BitStr = json2bitstring(binary_to_list(Str),FixedLength),
    Unused = (8 - (FixedLength rem 8)) band 7,
    {Unused,<<BitStr/bitstring,0:Unused>>}.


decode_jer_component([{Name,Type}|CompInfos],VMap,Acc) when is_map_key(Name,VMap) ->
    Value = maps:get(Name,VMap),
    Dec = decode_jer(Type,Value),
    decode_jer_component(CompInfos,VMap,[Dec|Acc]);
decode_jer_component([{_Name,_Type}|CompInfos],VMap,Acc) ->
    decode_jer_component(CompInfos,VMap,[asn1_NOVALUE|Acc]);
decode_jer_component([],_,Acc) ->
    lists:reverse(Acc).

%% This is the default representation of octet string i.e binary
json2octetstring2binary(Value) ->
    list_to_binary(json2octetstring(Value,[])).

%% This is the legacy_types representation of octet string i.e as a list
json2octetstring2string(Value) ->
    json2octetstring(Value,[]).

json2octetstring([A1,A2|Rest],Acc) ->
    Int = list_to_integer([A1,A2],16),
    json2octetstring(Rest,[Int|Acc]);
json2octetstring([], Acc) ->
    lists:reverse(Acc).

json2bitstring(Value,Length) ->
    json2bitstring(Value,Length,[]).

json2bitstring([A1,A2],Length,Acc) ->
    Int = list_to_integer([A1,A2],16) bsr (8-Length),
    Bin = list_to_binary(lists:reverse(Acc)),
    << Bin/binary,Int:Length>>;
json2bitstring([A1,A2|Rest],Length,Acc) ->
    Int = list_to_integer([A1,A2],16),
    json2bitstring(Rest,Length-8,[Int|Acc]).

bitstring2json(BitStr) when is_binary(BitStr) ->
    octetstring2json(binary_to_list(BitStr));
bitstring2json(BitStr) ->
    Pad = 8 - bit_size(BitStr) rem 8,
    NewStr = <<BitStr/bitstring,0:Pad>>,
    octetstring2json(binary_to_list(NewStr)).

octetstring2json(List) when is_list(List) ->
    list_to_binary([begin Num = integer_to_list(X,16), 
           if length(Num) == 1 -> "0"++Num;
              true -> Num
           end 
     end|| X<-List]).

