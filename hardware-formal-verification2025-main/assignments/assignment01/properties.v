// Instructions:
// - Implement the properties in this file.
// - Submit this file only.
// - Don't change the name of the file when submitting.

module properties(clk, rst, pedestrian_btn, car_light, pedestrian_light);
input clk;
input rst;
input wire pedestrian_btn;
input reg [1:0] car_light;
input reg pedestrian_light;
// Note that both car_light and pedestrian_light are defined as inputs above,
// even though they are defined as outputs in the module we want to monitor.

import state_pkg::*;

// *************** INSTRUCTION FOR PART A:   ***************
// *************** EDIT ONLY BELOW THIS LINE ***************
// *********************************************************
   
// NOTE: 
// - Don't change the property names (P1, P2, ...) below.
// - Don't change the labels (A1, A2, ...) below.
// - Edit only the lines where you see "EDIT HERE".
// - The answer for the first assert (A1) is given as an example.

// Example solution for the first specificaton:
property P1;
   (@(posedge clk) (car_light == RED || pedestrian_light == RED));
endproperty
A1: assert property (P1);

property P2;
   (@(posedge clk) (car_light==RED |=>(car_light==RED||car_light==GREEN)));
endproperty
A2: assert property (P2);

property P3;
   (@(posedge clk) (car_light==GREEN |=>(car_light==YELLOW||car_light==GREEN)));
endproperty
A3: assert property (P3);

property P4;
   (@(posedge clk) (car_light==YELLOW |=>(car_light==RED||car_light==YELLOW)));
endproperty
A4: assert property (P4);

property P5;
   (@(posedge clk) (car_light==RED || car_light==GREEN || car_light==YELLOW));
endproperty
A5: assert property (P5);

property P6;
   (@(posedge clk) (pedestrian_light==RED || pedestrian_light==GREEN));
endproperty
A6: assert property (P6);

property P7;
   (@(posedge clk) (pedestrian_light==GREEN |-> car_light==RED));
endproperty
A7: assert property (P7);

property P8;
   (@(posedge clk) (car_light==GREEN |-> pedestrian_light==RED));
endproperty
A8: assert property (P8);

property P9;
   (@(posedge clk) (pedestrian_light==GREEN |=> $past(car_light==RED))); //check later if the arrow is correct (do we need |-> or |=>)  
endproperty
A9: assert property (P9);

property P10;
   (@(posedge clk) (car_light==GREEN |=> $past(pedestrian_light==RED)));
endproperty
A10: assert property (P10);

property P11;
   (@(posedge clk) (car_light==GREEN |=> s_eventually(car_light!=GREEN)));
endproperty
A11: assert property (P11);

property P12;
   (@(posedge clk) (pedestrian_light==RED |=> s_eventually(pedestrian_light!=RED)));
endproperty
A12: assert property (P12);

// *************** EDIT ONLY ABOVE THIS LINE *****************

endmodule

// This binds the properties to traffic_light:
bind traffic_light properties properties_i(.*);
