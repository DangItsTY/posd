/** Sung-Min Park
 *  CS4240
 *  sp2cd
 */

import scala.swing._
import scala.swing.event._
import scala.util._
import java.awt.Color
import swing.{Panel, MainFrame, SimpleSwingApplication}
import java.awt.{Color, Graphics2D, Dimension}
import javax.swing.Timer

object gol extends SimpleSwingApplication{
	var mf_dim = new Dimension(480, 480)
	var bt_size = new Dimension(120, 120)
	var loc = new Point(245, 245)
	var sf_dim = new Dimension(120, 120)
	var long_dim = new Dimension(120, 120)
	var difficulty = (1.0).asInstanceOf[Double]
	
	var detected = false
	var white = new Color(255, 255, 255)

	object Mark extends Enumeration {
		type Mark = Value
		val alive = Value("alive")
		val dead = Value("dead")
	}

	var m1 = Mark.alive.toString
	
	object Cell extends Enumeration {
		type Cell = Value
		val C00 = Value("C00")
		val C01 = Value("C01")
		val C02 = Value("C02")
		val C03 = Value("C03")
		val C10 = Value("C10")
		val C11 = Value("C11")
		val C12 = Value("C12")
		val C13 = Value("C13")
		val C20 = Value("C20")
		val C21 = Value("C21")
		val C22 = Value("C22")
		val C23 = Value("C23")
		val C30 = Value("C30")
		val C31 = Value("C31")
		val C32 = Value("C32")
		val C33 = Value("C33")
		
	}
	
//	val all_cells = Cell.C00 :: Cell.C01 :: Cell.C02 :: Cell.C03 ::
//					Cell.C10 :: Cell.C11 :: Cell.C12 :: Cell.C13 ::
//					Cell.C20 :: Cell.C21 :: Cell.C22 :: Cell.C23 ::
//					Cell.C30 :: Cell.C31 :: Cell.C32 :: Cell.C33 :: Nil
	
	val all_cells = List("C00", "C01", "C02", "C03",
						 "C10", "C11", "C12", "C13",
						 "C20", "C21", "C22", "C23",
						 "C30", "C31", "C32", "C33")

	
	
	
				
	
	object Board extends Enumeration {
		
	}
	
//	val emptyboard = Mark.dead :: Mark.dead :: Mark.dead :: Mark.dead :: 
//					 Mark.dead :: Mark.dead :: Mark.dead :: Mark.dead :: 
//					 Mark.dead :: Mark.dead :: Mark.dead :: Mark.dead ::
//					 Mark.dead :: Mark.dead :: Mark.dead :: Mark.dead :: Nil
	
	val emptyboard = List("dead", "dead", "dead", "dead",
					"dead", "dead", "dead", "dead",
					"dead", "dead", "dead", "dead",
					"dead", "dead", "dead", "dead")
	
//	val b10 = Seq(Mark.dead, Mark.dead, Mark.dead, Mark.dead,
//					Mark.dead, Mark.alive, Mark.dead, Mark.dead,
//					Mark.dead, Mark.dead, Mark.dead, Mark.dead,
//					Mark.dead, Mark.dead, Mark.dead, Mark.dead);
	
	val b10 = List("dead", "dead", "dead", "dead",
					"dead", "alive", "dead", "dead",
					"dead", "dead", "dead", "dead",
					"dead", "dead", "dead", "dead")
	
	def game_update (b_old: List[String])(b_new: List[String])(cell_list: List[String]) : List[String] = {
	  cell_list match {
		case Nil =>  b_new
		case h :: t => game_update(b_old)( (apply_rules(b_old)(b_new)(h)) )(t)
	  }
	}
	
	def apply_rules (b_old: List[String])(b_new: List[String])(cell: String) : List[String] = {
	  cell match{
	    case "C00" if num_nei(b_old)(List("C01", "C10", "C11"))(cell) > 0  => (place(cell)("alive")(b_new));
	    case "C01" if num_nei(b_old)(List("C00", "C02", "C10", "C11", "C12"))(cell) > 0  => (place(cell)("alive")(b_new));
	    case "C02" if num_nei(b_old)(List("C01", "C03", "C11", "C12", "C13"))(cell) > 0  => (place(cell)("alive")(b_new));
	    case "C03" if num_nei(b_old)(List("C02", "C12", "C13"))(cell) > 0  => (place(cell)("alive")(b_new));
	    case "C10" if num_nei(b_old)(List("C00", "C01", "C11", "C20", "C21"))(cell) > 0  => (place(cell)("alive")(b_new));
	    case "C11" if num_nei(b_old)(List("C00", "C01", "C02", "C10", "C12", "C20", "C21", "C22"))(cell) > 0  => (place(cell)("alive")(b_new));
	    case "C12" if num_nei(b_old)(List("C01", "C02", "C03", "C11", "C13", "C21", "C22", "C23"))(cell) > 0  => (place(cell)("alive")(b_new));
	    case "C13" if num_nei(b_old)(List("C02", "C03", "C12", "C22", "C23"))(cell) > 0  => (place(cell)("alive")(b_new));
	    case "C20" if num_nei(b_old)(List("C10", "C11", "C21", "C30", "C31"))(cell) > 0  => (place(cell)("alive")(b_new));
	    case "C21" if num_nei(b_old)(List("C10", "C11", "C12", "C20", "C22", "C30", "C31", "C32"))(cell) > 0  => (place(cell)("alive")(b_new));
	    case "C22" if num_nei(b_old)(List("C11", "C12", "C13", "C21", "C23", "C31", "C32", "C33"))(cell) > 0  => (place(cell)("alive")(b_new));
	    case "C23" if num_nei(b_old)(List("C12", "C13", "C22", "C32", "C33"))(cell) > 0  => (place(cell)("alive")(b_new));
	    case "C30" if num_nei(b_old)(List("C20", "C21", "C31"))(cell) > 0  => (place(cell)("alive")(b_new));
	    case "C31" if num_nei(b_old)(List("C20", "C21", "C22", "C30", "C32"))(cell) > 0  => (place(cell)("alive")(b_new));
	    case "C32" if num_nei(b_old)(List("C21", "C22", "C23", "C31", "C33"))(cell) > 0  => (place(cell)("alive")(b_new));
	    case "C33" if num_nei(b_old)(List("C22", "C23", "C32"))(cell) > 0  => (place(cell)("alive")(b_new));
	    case _ => b_new
	  }
	}
		
	def num_nei(b: List[String])(list_neighbors: List[String])(c: String) : Int = {
	  list_neighbors match {
	    case Nil => 0
	    case h :: t => (get(b)(h)) match {
	      				case "alive" => 1 + num_nei(b)(t)(c)
	      				case "dead" => num_nei(b)(t)(c)
	    				}
	  }
	}
	
	def get(b: List[String])(c: String) : String = {
	  c match {
	    case "C00" => b(0)
	    case "C01" => b(1)
	    case "C02" => b(2)
	    case "C03" => b(3)
	    case "C10" => b(4)
	    case "C11" => b(5)
	    case "C12" => b(6)
	    case "C13" => b(7)
	    case "C20" => b(8)
	    case "C21" => b(9)
	    case "C22" => b(10)
	    case "C23" => b(11)
	    case "C30" => b(12)
	    case "C31" => b(13)
	    case "C32" => b(14)
	    case "C33" => b(15)
	    case _ => "undefined"
	  }
	}
	
	def place(cell: String)(m: String)(b: List[String]) : List[String] = {
	  cell match{
	    case "C00" => List(m, b(1), b(2), b(3), b(4), b(5), b(6), b(7), b(8), b(9), b(10), b(11), b(12), b(13), b(14), b(15));
	    case "C01" => List(b(0), m, b(2), b(3), b(4), b(5), b(6), b(7), b(8), b(9), b(10), b(11), b(12), b(13), b(14), b(15));
	    case "C02" => List(b(0), b(1), m, b(3), b(4), b(5), b(6), b(7), b(8), b(9), b(10), b(11), b(12), b(13), b(14), b(15));
	    case "C03" => List(b(0), b(1), b(2), m, b(4), b(5), b(6), b(7), b(8), b(9), b(10), b(11), b(12), b(13), b(14), b(15));
	    case "C10" => List(b(0), b(1), b(2), b(3), m, b(5), b(6), b(7), b(8), b(9), b(10), b(11), b(12), b(13), b(14), b(15));
	    case "C11" => List(b(0), b(1), b(2), b(3), b(4), m, b(6), b(7), b(8), b(9), b(10), b(11), b(12), b(13), b(14), b(15));
	    case "C12" => List(b(0), b(1), b(2), b(3), b(4), b(5), m, b(7), b(8), b(9), b(10), b(11), b(12), b(13), b(14), b(15));
	    case "C13" => List(b(0), b(1), b(2), b(3), b(4), b(5), b(6), m, b(8), b(9), b(10), b(11), b(12), b(13), b(14), b(15));
	    case "C20" => List(b(0), b(1), b(2), b(3), b(4), b(5), b(6), b(7), m, b(9), b(10), b(11), b(12), b(13), b(14), b(15));
	    case "C21" => List(b(0), b(1), b(2), b(3), b(4), b(5), b(6), b(7), b(8), m, b(10), b(11), b(12), b(13), b(14), b(15));
	    case "C22" => List(b(0), b(1), b(2), b(3), b(4), b(5), b(6), b(7), b(8), b(9), m, b(11), b(12), b(13), b(14), b(15));
	    case "C23" => List(b(0), b(1), b(2), b(3), b(4), b(5), b(6), b(7), b(8), b(9), b(10), m, b(12), b(13), b(14), b(15));
	    case "C30" => List(b(0), b(1), b(2), b(3), b(4), b(5), b(6), b(7), b(8), b(9), b(10), b(11), m, b(13), b(14), b(15));
	    case "C31" => List(b(0), b(1), b(2), b(3), b(4), b(5), b(6), b(7), b(8), b(9), b(10), b(11), b(12), m, b(14), b(15));
	    case "C32" => List(b(0), b(1), b(2), b(3), b(4), b(5), b(6), b(7), b(8), b(9), b(10), b(11), b(12), b(13), m, b(15));
	    case "C33" => List(b(0), b(1), b(2), b(3), b(4), b(5), b(6), b(7), b(8), b(9), b(10), b(11), b(12), b(13), b(14), m);
	    case _ => List()
	  }
	}
	
	def initialize(b: List[String])(l: List[String]) : List[String] = {
	  l match{
	    case Nil => b
	    case h :: t => initialize(place(h)("alive")(b))(t)
	  }
	}
	
	var list10 = List("C00")
	
	def initial_board1 = initialize(emptyboard)(list10)
	def initial_board2 = initialize(emptyboard)(list10)
	
	def do_play_game (b: List[String])(num: Int) : List[String] = {
	  if(num == 0) {
	    return b;
	  }
	  else {
	    do_play_game(game_update(b)(b)(all_cells))(num-1);
	  }
	}
	
	def play_game (l: List[String])(iterations: Int) : List[String] = {
	  return do_play_game(initialize(emptyboard)(l))(iterations)
	}

	
	def top = new MainFrame {
	  //var n = game_update(initial_board1)(initial_board2)(all_cells);
	  var data = Array.ofDim[Color](4, 4);
		
		//var a = 0
		for( a <- 0 until 2 ) {
	    var n = play_game(list10)(a);
	    
	    for(i <- 0 until 4) {
	    	for(j <- 0 until 4) {
	    		n(i*4+j) match {
	    		case "dead" => data(i)(j) = Color.WHITE;
	    		case "alive" => data(i)(j) = Color.BLACK;
	    		}
	    	}
	    }
	
	    
//	    Thread.sleep(500)
	    contents = new DataPanel(data) {
	    	preferredSize = new Dimension(300,300);
//	    	listenTo(mouse.clicks)
//	    	reactions += {
//				case e: MouseClicked =>
//				z += 1
//				println("Mouse clicked at " + e.point)
//				detected = false
//				println(detected)
//	    	}
	    }
		}
	   
	}
	 
}

class DataPanel(data: Array[Array[Color]]) extends Panel {

  override def paintComponent(g: Graphics2D) {
    val dx = g.getClipBounds.width.toFloat  / data.length
    val dy = g.getClipBounds.height.toFloat / data.map(_.length).max
    for {
      x <- 0 until data.length
      y <- 0 until data(x).length
      x1 = (x * dx).toInt
      y1 = (y * dy).toInt
      x2 = ((x + 1) * dx).toInt
      y2 = ((y + 1) * dy).toInt
    } {
      data(x)(y) match {
        case c: Color => g.setColor(c)
        case _ => g.setColor(Color.WHITE)
      }
      g.fillRect(x1, y1, x2 - x1, y2 - y1)
    }
  }
}

class ScalaTimer(val delay: Int) {
  val tmr: javax.swing.Timer = new javax.swing.Timer(delay, null)
  def start() = tmr.start()
  def stop() = tmr.stop()
}
