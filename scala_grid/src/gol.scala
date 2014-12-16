/** Sung-Min Park
 *  CS4240
 *  sp2cd
 */

import scala.swing._
import scala.swing.event._
import scala.util._

object gol extends SimpleSwingApplication{
	var mf_dim = new Dimension(480, 480)
	var bt_size = new Dimension(120, 120)
	var loc = new Point(245, 245)
	var sf_dim = new Dimension(120, 120)
	var long_dim = new Dimension(120, 120)
	var difficulty = (1.0).asInstanceOf[Double]
	var bg_start = getRandomColor()
	var detected = false
	var white = new Color(255, 255, 255)
	var black = new Color(0,0,0)
	var red = new Color(255,0,0)
	var green = new Color(0,255,0)
	var blue = new Color(0,0,255)
	var currentColor = white

	object Mark extends Enumeration {
		type Mark = Value
		val alive, dead = Value
	}
	
	var m1 = alive
	
	object Cell extends Enumeration {
		type Cell = Value
		val C00, C01, C02, C03,
			C10, C11, C12, C13,
			C20, C21, C22, C23,
			C30, C31, C32, C33 = Value
	}
	
	object Board extends Enumeration {
		
	}
	
	def mk_board() : Board {
	  
	}
	
	def top = new MainFrame {
		minimumSize = mf_dim
		maximumSize = mf_dim
		preferredSize = mf_dim
		contents = gp
		//background = new Color(255,255,255)
		//contents = ui
	}

	def getRandomColor() : Color = {
		var rr = Math.abs(Random.nextInt(255))
		var gg = Math.abs(Random.nextInt(255))
		var bb = Math.abs(Random.nextInt(255))
		var alpha = Math.abs(Random.nextInt(255))
		var hex = rr + gg + bb + alpha + ""
		return new Color(rr, gg, bb, alpha)
	}

	def gp = new GridPanel(4, 4) {
		background = bg_start
		var a = 1;
		for( a <- 1 until 17) {
			contents += grid
		}

		listenTo(mouse.clicks)
		reactions += {
			case e: MouseClicked =>
			  //background = getRandomColor()
			  println("Mouse clicked at " + e.point)
			  detected = false
			  println(detected)
		}
	}
	def grid = new Panel {
		minimumSize = sf_dim
		maximumSize = sf_dim
		preferredSize = sf_dim
		background = bg_start
		visible = true
		background = currentColor
		
		listenTo(mouse.clicks)
		reactions += {
			case e: MouseClicked =>
			  if(background == black) {
				  background = white
			  }
			  else if(background == white) {
				  background = black
			  }
			  println("Mouse clicked at " + e.point)
			  detected = false
			  println(detected)
		}
	}
}