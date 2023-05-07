declare

% Utilities
Car
Cdr
EncWithPrefix
Store
ReadFile
IsPrimitive
IsANumber
BuildTree

% String processing
LexAux
Lex
Infix2Prefix

% Node
Node
Preorder

% Template
Template

% Parsing
ParseBody
ParseSuperComb
ParseCall
ParseProgram

% Expression reduction
FindNext
Instantiate
ReplaceSuperComb
ReducePrimitive
Reduce

Test

% Utilities

fun {Car L}
    case L 
    of nil then nil
    [] H | _ then H
    end
end

fun {Cdr L}
    case L
    of nil then nil
    [] _ | R then R
    end
end

fun {EncWithPrefix Prefix Str}
    {String.toAtom {List.append Prefix {List.append "_" Str}}}
end

class Store
    attr values

    meth init
        values := {Dictionary.new}
    end

    meth add(Name Value)
        local Encoded = {EncWithPrefix "store" Name} in
            {Dictionary.put @values Encoded Value}
        end
    end

    meth find(Name $)
        local Encoded = {EncWithPrefix "store" Name} in
            {Dictionary.condGet @values Encoded nil}
        end
    end

    meth has(Name $)
        local Encoded = {EncWithPrefix "store" Name} in
            {Dictionary.member @values Encoded}
        end
    end
end

proc {ReadFile Path ?Result}
    local F in
        F = {New Open.file init(name:Path flags:[read])}
        {F read(list:Result size:all)}
        {F close}
    end
end

fun {IsPrimitive C}
    {List.member C ["+" "-" "*" "/"]}
end

fun {IsANumber Str}
    local
        AllDigits = fun {$ Y} {List.all Y Char.isDigit} end
        IntPart
        DecPart
    in
        {List.takeDropWhile Str fun {$ X} X \= &. end IntPart DecPart}
        {And {AllDigits IntPart} {AllDigits DecPart}}
    end
end

proc {BuildTree Env Joiner Lifter Tokens ?TreeOut}
    local
        fun {Join Trees}
            {List.foldL Trees Joiner nil}
        end

        proc {Aux Tokens TreePrev ?TreeOut ?Remaining}
            case Tokens
            of nil then Remaining = nil
            [] H | R then
                if {Or {IsPrimitive H} {Env has(H $)}} then
                    local
                        Break = {NewCell R}
                        Trees = {NewCell [{Lifter H}]}
                        N = if {IsPrimitive H} then 2 else {List.length {{Env find(H $)} args($)}} end
                    in
                        for I in 1..N do
                            local Tr B in
                                {Aux @Break nil Tr B}
                                Trees := Tr | @Trees
                                Break := B
                            end
                        end
                        TreeOut = {Join (TreePrev | {List.reverse @Trees})}
                        Remaining = @Break
                    end
                else
                    local ToLift = if {IsANumber H} then {String.toFloat H} else H end in
                        TreeOut = {Joiner TreePrev {Lifter ToLift}}
                    end
                    Remaining = R
                end
            end
        end

        Dummy
    in
        {Aux {Infix2Prefix Tokens} nil TreeOut Dummy}
    end
end

%------------

% String processing

fun {LexAux Stream Tokens Carry}
    local
        Keywords = ["fun" "let" "in" "+" "-" "*" "/" "=" "(" ")"]

        fun {CaptureSymbol}
            if Carry \= nil then {Reverse Carry} | Tokens
            else Tokens
            end
        end

        fun {CaptureKeyword}
            local Match = fun {$ Keyword} {List.isPrefix Keyword Stream} end in
                {Car {List.filter Keywords Match}}
            end
        end
    in
        if Stream \= nil then 
            local Keyword = {CaptureKeyword} in
                if Keyword \= nil then
                    local Forward = {List.drop Stream {List.length Keyword}} in
                        {LexAux Forward (Keyword | {CaptureSymbol}) nil}
                    end
                else
                    local H | R = Stream in
                        if {Char.isSpace H} then
                            {LexAux R {CaptureSymbol} nil}
                        else
                            {LexAux R Tokens (H | Carry)}
                        end
                    end
                end
            end
        else
            {CaptureSymbol}
        end
    end
end

fun {Lex Stream}
    {List.reverse {LexAux Stream nil nil}}
end

fun {Infix2Prefix Data}
    local Reverse Infix2Postfix in
        fun {Reverse Data Ans}
            case Data of H|T then
                case H of "(" then
                    {Reverse T ")"|Ans}
                []  ")" then
                    {Reverse T "("|Ans}
                else
                    {Reverse T H|Ans}
                end
            else
                Ans
            end
        end
        fun {Infix2Postfix Data Stack Res}
            local PopWhile in
                fun {PopWhile Stack Res Cond}
                    case Stack of H|T then
                        if {Cond H} then
                            {PopWhile T H|Res Cond}
                        else
                            [Res Stack]
                        end
                    else
                        [Res Stack]
                    end
                end
                case Data of H|T then
                    case H of "(" then
                        {Infix2Postfix T H|Stack Res}
                    [] ")" then
                        local H2 T2 T3 in
                            H2|T2|nil = {PopWhile Stack Res fun {$ X} {Not X=="("} end}
                            _|T3 = T2
                            {Infix2Postfix T T3 H2}
                        end 
                    [] "+" then
                        local H2 T2 in
                            H2|T2|nil = {PopWhile Stack Res fun {$ X} {List.member X ["*" "/"]} end}
                            {Infix2Postfix T H|T2 H2}
                        end
                    [] "-" then
                        local H2 T2 in
                            H2|T2|nil = {PopWhile Stack Res fun {$ X} {List.member X ["*" "/"]} end}
                            {Infix2Postfix T H|T2 H2}
                        end
                    [] "*" then
                        local H2 T2 in
                            H2|T2|nil = {PopWhile Stack Res fun {$ X} {List.member X nil} end}
                            {Infix2Postfix T H|T2 H2}
                        end
                    [] "/" then
                        local H2 T2 in
                            H2|T2|nil = {PopWhile Stack Res fun {$ X} {List.member X nil} end}
                            {Infix2Postfix T H|T2 H2}
                        end
                    else
                        {Infix2Postfix T Stack H|Res}
                    end
                else 
                    Res
                end
            end
        end
        {Infix2Postfix "("|{Reverse "("|Data nil} nil nil}
    end
end

%------------

% Node related definitions

class Node
    attr val left right
    
    meth init(Value)
        val := Value
        left := nil
        right := nil
    end

    meth setLeft(Left)
        left := Left
    end

    meth setRight(Right)
        right := Right
    end

    meth val($)
        @val
    end

    meth isReduce($)
        {Number.is @val}
    end

    meth setVal(Value)
        val := Value
    end

    meth left($)
        @left
    end

    meth right($)
        @right
    end

    meth replace(R)
        {self setVal({R val($)})}
        {self setLeft({R left($)})}
        {self setRight({R right($)})}
    end
end

proc {Preorder Node}
    local
        fun {Aux Node Acc}
            if Node \= nil then
                local Step1 Step2 in
                    Step1 = {Node val($)} | Acc
                    Step2 = {Aux {Node left($)} Step1}
                    {Aux {Node right($)} Step2}
                end
            else
                Acc
            end
        end
    in
        {Browse {List.reverse {Aux Node nil}}}
    end
end

%-------------

% Template related definitions

class Template
    attr args bindings body

    meth init
        args := nil
        bindings := {Dictionary.new}
        body := nil
    end

    meth args($)
        @args
    end

    meth setArgs(Args)
        args := Args
    end

    meth hasArg(Name $)
        {List.member Name @args}
    end

    meth addBinding(Id Body)
        local Encoded = {EncWithPrefix "binding" Id} in
            {Dictionary.put @bindings Encoded Body}
        end
    end

    meth hasBinding(Id $)
        local Encoded = {EncWithPrefix "binding" Id} in
            {Dictionary.member @bindings Encoded}
        end
    end

    meth body($)
        @body
    end

    meth setBody(Body)
        body := Body
    end
end

%-------------

% Expression evaluation 

fun {FindNext Expr}
    local
        fun {Aux Current Acc}
            if Current == nil then Acc
            else {Aux {Current left($)} (Current | Acc)}
            end
        end
    in
        {Aux Expr nil}
    end
end

% Arguably the most important method throughout the whole program
proc {Instantiate Temp Root}
    local
        ArgBindings = {New Store init}
        IntBindings = {New Store init}

        proc {Aux NodeIn ?NodeOut}
            case NodeIn
            of nil then NodeOut = nil
            [] app(L R) then
                local Left Right in
                    {Aux L Left}
                    {Aux R Right}
                    NodeOut = {New Node init(app)}
                    {NodeOut setLeft(Left)}
                    {NodeOut setRight(Right)}
                end
            [] Value then
                if {Or {Number.is Value} {IsPrimitive Value}} then
                    NodeOut = {New Node init(Value)}
                elseif {Temp hasBinding(Value $)} then
                    if {IntBindings has(Value $)} then
                        NodeOut = {IntBindings find(Value $)}
                    else
                        NodeOut = {Aux {Temp getBinding(Value $)}}
                        {IntBindings add(Value NodeOut)}
                    end
                elseif {Temp hasArg(Value $)} then
                    if {ArgBindings has(Value $)} then
                        NodeOut = {ArgBindings find(Value $)}
                    else
                        NodeOut = {New Node init(Value)}
                        {ArgBindings add(Value NodeOut)}
                    end
                end
            end
        end

        proc {ZipArgs Current Args}
            case Args
            of nil then skip
            [] H | R then
                local
                    AB = {ArgBindings find(H $)}
                    ToZip = {Current right($)}
                    Next = {Current left($)}
                in
                    {AB replace(ToZip)}
                    {ZipArgs Next R}
                end
            end
        end

        Instance = {Aux {Temp body($)}}
    in
        {ZipArgs Root {List.reverse {Temp args($)}}}
        {Root replace(Instance)}
    end
end

proc {ReplaceSuperComb Env Stack Name}
    local
        Temp = {Env find(Name $)}
        Root = {Car {List.drop Stack {List.length {Temp args($)}}}}
    in
        {Instantiate Temp Root}
    end
end

proc {ReducePrimitive Env Stack Primitive}
    local
        Op = case Primitive
            of "+" then fun {$ X Y} X + Y end
            [] "-" then fun {$ X Y} X - Y end
            [] "*" then fun {$ X Y} X * Y end
            [] "/" then fun {$ X Y} X / Y end
        end

        Root = {Car {List.drop Stack 2}}
        Arg1 = {{Root left($)} right($)}
        Arg2 = {Root right($)}
    in
        if {Not {Arg1 isReduce($)}} then
            {Reduce Env Arg1}
        end

        if {Not {Arg2 isReduce($)}} then
            {Reduce Env Arg2}
        end

        {Root setLeft(nil)}
        {Root setRight(nil)}

        local Result = {Op {Arg1 val($)} {Arg2 val($)}} in
            {Root setVal(Result)}
        end
    end
end

proc {Reduce Env Expr}
    local
        Stack = {FindNext Expr}
        Next = {{Car Stack} val($)}
        IsSuperComb = fun {$ Name} {Env has(Name $)} end
    in
        if {IsPrimitive Next} then
            {ReducePrimitive Env Stack Next}
        elseif {IsSuperComb Next} then
            {ReplaceSuperComb Env Stack Next}
            {Reduce Env Expr}
        end
    end
end

%-----------

% Parsing

proc {ParseBody Env Tokens ?Result}
    local
        fun {Joiner Prev Curr}
            if Prev \= nil then
                app(Prev Curr)
            else
                Curr
            end
        end

        fun {Lifter Value}
            Value
        end
    in
        {BuildTree Env Joiner Lifter Tokens Result}
    end
end

proc {ParseSuperComb Env Line}
    local
        Temp = {New Template init}
        Parts = {String.tokens Line &=}
        Sig = {Lex {List.nth Parts 1}}
        Name | Args = Sig
        Def = {Lex {List.nth Parts 2}}
    in
        {Temp setArgs(Args)}
        {Temp setBody({ParseBody Env Def})}
        {Env add(Name Temp)}
    end
end

proc {ParseCall Env Line ?Expr}
    local
        proc {Joiner Prev Curr ?Joined}
            if Prev \= nil then
                Joined = {New Node init(app)}
                {Joined setLeft(Prev)}
                {Joined setRight(Curr)}
            else
                Joined = Curr
            end
        end

        fun {Lifter Value}
            {New Node init(Value)}
        end

        Tokens = {Lex Line}
    in
        {BuildTree Env Joiner Lifter Tokens Expr}
    end
end

proc {ParseProgram Stream}
    local
        Lines = {String.tokens Stream &\n}
        Size = {List.length Lines}
        SuperCombs = {List.take Lines (Size-1)}
        Call = {List.last Lines}

        Env = {New Store init}
    in
        for S in SuperCombs do
            {ParseSuperComb Env S}
        end

        local Expr = {ParseCall Env Call} in
            {Reduce Env Expr}
            {Preorder Expr}
        end
    end
end

%-----------

proc {Test}
    {ParseProgram {ReadFile "testcases/simple.txt"}}
end

{Test}