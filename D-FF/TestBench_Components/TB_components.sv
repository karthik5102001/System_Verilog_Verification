
/////////////////////--INTERFACE--///////////////////

interface D_IF(input bit clock);        ///giving clock to inerface as input 
  
  bit [3:0] din;                        ///2^4 = 16 values can be alloted
  bit [3:0]  dout;
  logic  reset;
  
  clocking mon2int @(posedge clock);   ///clocking block
    default input #1 output #1;        ///defining the input and output skew 
    input dout;                        ///dout is input with respect to testbench
    output din;                        ///din is output whith respect to testbench
    output reset;                      ///same as reset also respect to testbench
  endclocking
  
  
  modport M2I (input clock, reset, din, output dout);    ///modport defines input and output of interface
  
endinterface



////////////////////--TRANSACTION--/////////////////////

class transaction;
  
  rand bit [3:0]  din;                        ///randomize input when ever we call
   bit [3:0] dout;
   bit reset;
  logic clock;
  
  function void display(input string str);           ///to display when ever we call
    $display("[%0s] : din = %0d , dout = %0d , reset = %0d",str,din,dout,reset);
  endfunction
  
  function transaction copy();                      ///emergency deep copy
    copy = new();
    copy.din = this.din;
    copy.dout = this.dout;
    copy.reset = this.reset;
  endfunction
  
endclass


///////////////////--GENERATOR--//////////////////////


class generator ;                            ///generator generate signals to DUV
  
  event gen_done;                            ///triggers when generator does it work
  event score_board_done;                    ///get's the signal when scoreboard finish it's work 
  
  int count;                                 
  
  transaction trans_gen;
  
  mailbox #(transaction) gen2driv;          ///generator to driver
  mailbox #(transaction) gen2refM;          ///generator to refernce module
  
  function new(mailbox #(transaction) gen2driv, mailbox #(transaction) gen2refM);
                                            ///assigning values local variable
    this.gen2driv = gen2driv;                       
    this.gen2refM = gen2refM;
    trans_gen = new();
    
    endfunction
  
  
  task run();
    
    repeat(count)
      begin
        assert(trans_gen.randomize()) else $display("FAILED");    ///Randomize when we call
        
        gen2driv.put(trans_gen.copy);                             ///deep copy the transaction class
        gen2refM.put(trans_gen.copy);
        
        $display("[GEN] : DOne putting data to mailbox ");         ///comfirm display
        trans_gen.display("GEN");
        @(score_board_done);                                       ///wait for scoreboard to finish its work
      end
    ->gen_done;                                                    ///alert the task to finish
    
  endtask
  
  
endclass


//////////////////////--DRIVER--////////////////////////////


class driver;
   
   event drive_done;                                             ///to info when driver is done
   
   transaction trans_driv;
  
  virtual D_IF.M2I i_ff_driver;                                 ///virtual interface D_IF.M2I
  
  mailbox #(transaction) gen2driv; 
  
  function new( mailbox #(transaction) gen2driv);
    
    this.gen2driv = gen2driv;
    trans_driv = new();
    
  endfunction
  
  
  task reset();
    
    i_ff_driver.reset <= 1;                               ///reseting
    
    repeat(3) @(posedge i_ff_driver.clock); 
    
    trans_driv.display("RESET");
    
    i_ff_driver.reset <= 0;
    
    @(posedge i_ff_driver.clock);
    $display("RESET DONE");
    
  endtask
  
  task run();
    
    forever begin
      gen2driv.get(trans_driv);                          ///getting the signals from driver
        
    i_ff_driver.din <=  trans_driv.din;                  ///driving to initerface
    i_ff_driver.din <=  trans_driv.din;
      @(posedge i_ff_driver.clock);
    $display("The Driver has done its work");
    trans_driv.display("DRV");
    end
    
  endtask
  
endclass

////////////////////--MONITOR--///////////////////////////

class monitor;
  
  event monitor_done;
   
   transaction trans_moni;
  
  virtual D_IF.M2I i_ff_moni;
  
  mailbox #(transaction) moni2ref;                    ///monitor to refrence
  
  function new( mailbox #(transaction) moni2ref);
    
    this.moni2ref = moni2ref;
    trans_moni = new();
    
  endfunction
  
  
  task run();
    
    forever begin
      repeat(2) @(posedge i_ff_moni.clock)
        
      trans_moni.dout = i_ff_moni.dout;                 ///taks the value from the interface
      moni2ref.put(trans_moni.copy);                    ///deep copy the transaction
      $display("[MON] : Data has delivered to ref model");
      trans_moni.display("MON");      
      
    end
    
  endtask
  
endclass

///////////////////--REFRENCE-MODULE//////////////////////////



class Refrence_module;
  
  mailbox #(transaction) moni2ref;
  mailbox #(transaction) gen2ref;
  mailbox #(transaction) ref2scrb;
  
  static int valid;
  static int in_valid;
  
  event ref2gen;
  
  transaction trasn_gen2rm;
  transaction trans_moni2rm;
  transaction trans_rm2scrb;

  function new(mailbox #(transaction) moni2ref,
               mailbox #(transaction) gen2ref );
    
    this.moni2ref = moni2ref;
    this.gen2ref = gen2ref;

    
  endfunction
  
  
  task compare(transaction trans_checker);
    if(trasn_gen2rm.din == trans_checker.dout)          ////comparing the generator din value and data from monitor
      begin
        $display("[RM] : DATA MATCHED");                
        $display("DOUT IS %0d",trans_moni2rm.dout);
        valid++;
      end
    else 
      begin
      $display("[RM] : DATA MISSS-MATCHED");
         $display("DOUT IS %0d",trans_moni2rm.dout);
        in_valid++;
      end
    
  endtask
  
  task result();
    
     $display("@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@");
    $display("THE VLAID COUNT IS %0d",valid);
    $display("THE IN-VLAID COUNT IS %0d",in_valid);
    $display("@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@");
    ->ref2gen;
    
  endtask
  
  task run();
    
    forever begin
      gen2ref.get(trasn_gen2rm);
      moni2ref.get(trans_moni2rm);
      compare(trans_moni2rm); 
      result();
    //  ref2scrb.put(trans_moni2rm);
    end
 
  endtask
  
  
endclass

/////////////////////--ENVIRONMENT--///////////////////////////


class environment;
  transaction trans;
  generator gen;
  driver driv;
  monitor moni;
  Refrence_module  ref_mod;
   
  
  
  mailbox #(transaction) gen2drive;
  mailbox #(transaction) gen2ref;
  mailbox #(transaction) moni2ref;
 
  virtual D_IF.M2I i_ff;
 
  function new(virtual D_IF.M2I i_ff);         /// adding the interface to virtual interface
    gen2drive = new();                         ///objectifying the mailboxs
    gen2ref = new();
    moni2ref = new();
    
    this.i_ff = i_ff;                          ///handling interface to local interface
    
    gen = new(gen2drive,gen2ref);              ///assigning mailbox to all the classes
    driv = new(gen2drive);
    moni = new(moni2ref);
    ref_mod = new(moni2ref,gen2ref);
    
    driv.i_ff_driver = i_ff;                  ///assigning the interafce to driver and monitor 
    moni.i_ff_moni = i_ff;
    
    ref_mod.ref2gen = gen.score_board_done;    
    
    endfunction

  task pre_test();
    driv.reset(); 
  endtask
  
  task test();
    fork
      gen.run(); // Start generator
      driv.run(); // Start driver
      moni.run(); // Start monitor
      ref_mod.run();
    
    join_any
  endtask
  
  task post_test();
    wait(gen.gen_done.triggered); // Wait for generator to complete
    $finish();                    // Finish simulation
  endtask
  
  task run();
    pre_test();                   // Run pre-test setup
    test();                        // Run the test
    post_test();                // Run post-test cleanup
  endtask

endclass



/////////////////////--TOP-MODULE--//////////////////////////
  
 module tb;
   
   bit clock;
   
   D_IF d_if(clock);                     ///defining the interface      
 
   dff dut(d_if);                        ///defining the DUV
  
  initial begin
    clock <= 0; 
  end
  
  always #10 clock <= ~clock; 
  
  environment env; 
 
  initial begin
    env = new(d_if);                          //// Initialize the environment with the DUT interface
    env.gen.count = 10;                      //// Set the generator's stimulus count
    env.run();                               //// Run the environment
  end
  
  initial begin
    $dumpfile("dump.vcd");                    /// Specify the VCD dump file
    $dumpvars;                                /// Dump all variables
  end
endmodule