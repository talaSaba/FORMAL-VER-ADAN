import elevator_pkg::*;

module properties #(parameter FLOORS = 5)
(
    input logic              clk,
    input logic              rst,
    input logic [FLOORS-1:0] requestFloor,
    input logic [FLOORS-1:0] currentFloor,
    input logic [FLOORS-1:0] floorLight,
    input                    Direction direction,
    input                    DoorsOp doorsOp,
    input                    EngineOp engineOp
);
 //###############################################################
//aux for q1.2
logic after_reset_1cycle;

always_ff @(posedge clk) begin
  if (rst) after_reset_1cycle <= 1'b1;
  else after_reset_1cycle <= 1'b0;
end

property prop_Q1b;
  @(posedge clk) after_reset_1cycle |-> $onehot(currentFloor);
endproperty
assume_Q1b: assume property (prop_Q1b);


//###############################################################
//what did we do : we initialised a new register called first_c and 
//we initialized it w 1 and with each clock rise we put 0 in it , so
// we can check 1.2 with onehot ONE time at the begining 
 //###############################################################


// ASSUME 1: Assume elevator moves up if engineOp is UP.
property prop_1;
    @(posedge clk) (engineOp == GO) && (direction == UP) |=> (currentFloor == $past(currentFloor << 1));
endproperty
assume_1: assume property (prop_1);

// ASSUME 2: Assume elevator moves down if engineOp is DOWN.
property prop_2;
    @(posedge clk) (engineOp == GO) && (direction == DOWN) |=> (currentFloor == $past(currentFloor >> 1));
endproperty
assume_2: assume property (prop_2);

// QUESTION 1(a): Assume elevator doesn't move if engineOp is STOP.
property prop_Q1a;
    @(posedge clk) (engineOp == STOP)|=> (currentFloor==$past(currentFloor)); // DONE
endproperty
assume_Q1a: assume property (prop_Q1a);


// QUESTION 2: Check we don't hit the basement.
property prop_Q2;
    @(posedge clk) ( $onehot(currentFloor)&&currentFloor[0]&&engineOp==GO |-> !(direction==DOWN)); // EDIT THIS LINE
endproperty
assert_Q2: assert property (prop_Q2);

// QUESTION 3: Check we don't hit the roof.
property prop_Q3;
    @(posedge clk)  ( $onehot(currentFloor)&&currentFloor[FLOORS-1]&&engineOp==GO |-> !(direction==UP));
endproperty
assert_Q3: assert property (prop_Q3);

// QUESTION 4: Check door safety.
property prop_Q4;
    @(posedge clk) doorsOp==OPEN|->engineOp==STOP ; // EDIT THIS LINE
endproperty
assert_Q4: assert property (prop_Q4);

// QUESTION 5:
property prop_Q5;
    @(posedge clk) 
    (requestFloor[0]) |-> ##[1:$](currentFloor[0]&&(engineOp == STOP)&&(doorsOp == OPEN));
endproperty 
assert_Q5: assert property (prop_Q5);

// QUESTION 6:
property prop_Q6;
    @(posedge clk)(floorLight[0]&&!currentFloor[0])[*40] ;// EDIT THIS LINE
endproperty
cover_Q6: cover property (prop_Q6);

// QUESTION 7:
property prop_Q7;
    @(posedge clk)(!(engineOp==GO && direction==DOWN)) 
    throughout(
      ##[0:$]( $onehot(currentFloor) && currentFloor[0] &&engineOp==STOP && doorsOp==OPEN )
##[0:$](##[0:$](engineOp==GO && direction==UP)##1($onehot(currentFloor)&&engineOp==STOP&&doorsOp==OPEN &&(currentFloor==$past(currentFloor<<1))))[*(FLOORS-1)]
##0($onehot(currentFloor) && currentFloor[FLOORS-1]&&engineOp==STOP && doorsOp==OPEN ));
endproperty
cover_Q7: cover property (prop_Q7);

// QUESTION 8:
property prop_Q8;
    @(posedge clk)(!(engineOp==GO && direction==UP))throughout(##[0:$]($onehot(currentFloor)&&currentFloor[FLOORS-1]&&engineOp==STOP&&doorsOp==OPEN)##[0:$](##[0:$] (engineOp==GO && direction==DOWN)
##1( $onehot(currentFloor)&&engineOp==STOP && doorsOp==OPEN&&(currentFloor == $past(currentFloor >> 1))))[* (FLOORS-1)]
##0($onehot(currentFloor) && currentFloor[0]&&engineOp==STOP && doorsOp==OPEN));
endproperty
cover_Q8: cover property (prop_Q8);

// QUESTION 9:
property prop_Q9;
    @(posedge clk)
    
    //Q7****************************************************************
    ((!(engineOp==GO && direction==DOWN)) throughout(##[0:$] ($onehot(currentFloor)&&currentFloor[0]&&engineOp==STOP && doorsOp==OPEN )
##[0:$](##[0:$] (engineOp==GO && direction==UP)##1($onehot(currentFloor)&&engineOp==STOP&&doorsOp==OPEN&&(currentFloor==$past(currentFloor<< 1))))[*(FLOORS-1)]
##0($onehot(currentFloor)&&currentFloor[FLOORS-1]&&engineOp==STOP&&doorsOp==OPEN)))


##1


// this isi the "immediatly after "



    // Q8 BEGIN ******************************************************8



((!(engineOp==GO && direction==UP)) throughout(
##[0:$] ( $onehot(currentFloor)&& currentFloor[FLOORS-1] &&
engineOp==STOP && doorsOp==OPEN)

##[0:$]
(##[0:$] (engineOp==GO && direction==DOWN)##1($onehot(currentFloor) &&engineOp==STOP && doorsOp==OPEN &&(currentFloor == $past(currentFloor >> 1)))
)[*(FLOORS-1)]##0($onehot(currentFloor) && currentFloor[0] &&engineOp==STOP && doorsOp==OPEN)))
 ;
  
endproperty
cover_Q9: cover property (prop_Q9);

endmodule

bind elevator properties #(.FLOORS(FLOORS)) properties_i(.*);
