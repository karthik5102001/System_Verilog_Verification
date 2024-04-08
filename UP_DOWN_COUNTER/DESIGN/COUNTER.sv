////////////////////////////////////////////////RTL/////////////////////////////////////////////

module up_DW_counter( clock,din,load,mode,reset, count);
  input clock;
  input  [3:0] din;
  input load,mode,reset;
  output reg [3:0] count = 0;
  
  always @(posedge clock)
    begin
   if(reset == 1)
        count <= 0;
    else if (load == 1)
        count <= din;
    else if(mode == 1)
        begin
          if (count >= 11)
           count <= 4'b0;
          else 
        count <= count + 1'b1;
        end
  else
    begin
      if(count == 0)
        count <= 4'd11;
      else 
        count <= count - 1'b1;
    end
    end
endmodule


/*
module test();
 
   reg clock;
   reg [3:0] din;
   reg load;
   reg mode;
   reg reset;
   wire [3:0] count;
   parameter timee = 5;

  up_DW_counter dut(.clock(clock), .din(din), .load(load), .mode(mode), .reset(reset), .count(count));

    task initiall();
    din = 0;
    load = 0;
    mode = 0;
    reset = 0;
    //count = 0;
 
     endtask


   task reset_1();
      reset = 1;
      #(timee);
      reset = 0;
   endtask

   task mode_1();
     mode = 1;
   endtask


   task mode_0();
     mode = 0;
   endtask

 
   task load_1(input loadd);
      load = 1;
      din = loadd;
       load = 0;
    endtask

  initial begin
    clock = 0;
   forever #(timee) clock = ~ clock; 
    end
 
  initial begin
    initiall();
    reset_1();
    #((timee)/2);
     mode_1();
    #50;
     mode_0();
    #50;
     load_1(4);
    #50;
     reset_1();
    #50;
     #200 $finish;
   end 

initial $monitor($time,"the reset=%0d \t mode = %0d \t load = %0d \t din = %0d \t count = %0d",reset,mode,load,din,count);
endmodule
